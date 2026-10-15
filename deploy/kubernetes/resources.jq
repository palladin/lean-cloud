# Credential-free, ordinary Kubernetes resources. All node volumes are retained.
. as $c |
def labels($role): {"app.kubernetes.io/managed-by":"lean-cloud","lean-cloud/deployment":$c.name} +
  (if $role=="" then {} else {"lean-cloud/role":$role} end);
def meta($name;$role): {name:$name,namespace:$c.namespace,labels:labels($role)};
def resource($api;$kind;$name;$role): {apiVersion:$api,kind:$kind,metadata:meta($name;$role)};
def claim: {accessModes:["ReadWriteOnce"],storageClassName:$c.storageClass,resources:{requests:{storage:(($c.diskGiB|tostring)+"Gi")}}};
def probe: {httpGet:{path:"/health",port:"http"},timeoutSeconds:3,periodSeconds:5};
def service($role): resource("v1";"Service";$role;$role) + {spec:{type:"ClusterIP",publishNotReadyAddresses:true,selector:labels($role),ports:[{name:"http",port:8080,targetPort:"http"}]}};
def node($role): resource("apps/v1";"StatefulSet";$role;$role) + {spec:{
  serviceName:$role,replicas:0,selector:{matchLabels:labels($role)},updateStrategy:{type:"OnDelete"},
  persistentVolumeClaimRetentionPolicy:{whenDeleted:"Retain",whenScaled:"Retain"},
  template:{metadata:{labels:(labels($role)+($c.podLabels//{}))},spec:{
    serviceAccountName:"cloud-node",automountServiceAccountToken:false,terminationGracePeriodSeconds:60,
    nodeSelector:{"kubernetes.io/os":"linux"},
    securityContext:{runAsNonRoot:true,runAsUser:10001,runAsGroup:10001,fsGroup:10001,seccompProfile:{type:"RuntimeDefault"}},
    containers:[{name:"node",image:$c.image,imagePullPolicy:"IfNotPresent",
      args:[(if $role=="scheduler" then "serve-scheduler" else "serve-worker" end),"/etc/lean-cloud/config.json"],
      env:([{name:"CLOUD_INBOX_DATABASE",value:"/data/inbox.sqlite"},
        {name:"CLOUD_NODE_NAME",valueFrom:{fieldRef:{fieldPath:"spec.nodeName"}}}]+
        (if $role=="scheduler" then [] else [{name:"CLOUD_WORKER_ID",value:$role}] end)),
      ports:[{name:"http",containerPort:8080}],
      resources:{requests:{cpu:(($c.cpuMillis|tostring)+"m"),memory:(($c.memoryMiB|tostring)+"Mi")},limits:{memory:(($c.memoryMiB|tostring)+"Mi")}},
      securityContext:{allowPrivilegeEscalation:false,readOnlyRootFilesystem:true,capabilities:{drop:["ALL"]}},
      startupProbe:(probe+{failureThreshold:60}),readinessProbe:probe,livenessProbe:(probe+{failureThreshold:6}),
      volumeMounts:[{name:"state",mountPath:"/data"},{name:"configuration",mountPath:"/etc/lean-cloud",readOnly:true},{name:"temporary",mountPath:"/tmp"}]}],
    volumes:[{name:"configuration",secret:{secretName:"cloud-config",defaultMode:288}},{name:"temporary",emptyDir:{}}]}},
  volumeClaimTemplates:[{metadata:{name:"state",labels:labels($role)},spec:claim}]}};
(["scheduler"] + [range(1;$c.workers+1)|"worker\(.)"]) as $roles |
{apiVersion:"v1",kind:"List",items:([
  {apiVersion:"v1",kind:"Namespace",metadata:{name:$c.namespace,labels:labels("")}},
  (resource("v1";"ServiceAccount";"cloud-node";"")|.metadata.annotations=($c.serviceAccountAnnotations//{})|.automountServiceAccountToken=false),
  (service("scheduler")|.metadata.name="cloud-api")
] + [$roles[] as $r | service($r),node($r),
  (resource("v1";"PersistentVolumeClaim";("state-"+$r+"-0");$r)+{spec:claim})])}
