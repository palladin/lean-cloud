# Separate ingest Job: no scheduler/worker CPU or scratch disk is used for import.
. as $c |
def meta($name): {name:$name,namespace:$c.namespace,
  labels:{"lean-cloud/wiki-ingest":$c.owner}};
{apiVersion:"v1",kind:"List",items:[
  {apiVersion:"v1",kind:"PersistentVolumeClaim",metadata:meta("wiki-import"),
   spec:{accessModes:["ReadWriteOnce"],storageClassName:$c.storageClass,
     resources:{requests:{storage:"64Gi"}}}},
  {apiVersion:"batch/v1",kind:"Job",metadata:meta("wiki-import"),spec:{
    backoffLimit:0,activeDeadlineSeconds:86400,
    template:{metadata:{labels:(($c.podLabels // {})+{"lean-cloud/wiki-ingest":$c.owner})},spec:{
      restartPolicy:"Never",serviceAccountName:"cloud-node",automountServiceAccountToken:false,
      securityContext:{runAsNonRoot:true,runAsUser:10001,runAsGroup:10001,fsGroup:10001,
        seccompProfile:{type:"RuntimeDefault"}},
      containers:[{name:"import",image:$c.image,
        command:["bash","/source/ingest.sh","/source/snapshot.json","/etc/lean-cloud/config.json","/data"],
        resources:{requests:{cpu:"500m",memory:"1Gi"},limits:{cpu:"1",memory:"2Gi"}},
        securityContext:{allowPrivilegeEscalation:false,readOnlyRootFilesystem:true,capabilities:{drop:["ALL"]}},
        volumeMounts:[{name:"data",mountPath:"/data"},{name:"temporary",mountPath:"/tmp"},
          {name:"source",mountPath:"/source",readOnly:true},{name:"configuration",mountPath:"/etc/lean-cloud",readOnly:true}]}],
      volumes:[{name:"data",persistentVolumeClaim:{claimName:"wiki-import"}},
        {name:"source",configMap:{name:"wiki-import"}},
        {name:"configuration",secret:{secretName:"cloud-config",defaultMode:288}},
        {name:"temporary",emptyDir:{sizeLimit:"1Gi"}}]}}}}
]}
