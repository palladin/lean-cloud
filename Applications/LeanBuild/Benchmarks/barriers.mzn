% Restricted optimization: keep incumbent unit-task start times, optimize
% worker placement and barrier positions. This is not a global DAG optimum.
int: n;
int: workers;
array[1..workers] of int: cpus;
int: edges;
array[1..edges] of int: src;
array[1..edges] of int: dst;
int: max_rounds;
int: horizon;
int: penalty;
int: upper;
array[1..n] of int: hint_round;
array[1..n] of int: hint_worker;
array[1..n] of int: hint_start;
array[1..max_rounds] of int: hint_duration;
array[1..n] of int: earliest;
array[1..n] of int: tail_length;

int: span = max(hint_start) + 1;
int: incumbent_rounds = max(hint_round);
array[0..span-1] of var 1..incumbent_rounds: phase :: no_output;
array[1..n] of var 1..workers: worker :: add_to_output;
array[1..n] of var 1..max_rounds: round :: add_to_output = [phase[hint_start[i]] | i in 1..n];
array[1..n] of var 0..horizon-1: start :: add_to_output = hint_start;
array[1..max_rounds] of var 0..span: duration :: add_to_output =
  [sum(t in 0..span-1)(bool2int(phase[t] = r)) | r in 1..max_rounds];
array[0..span-1] of int: hint_phase =
  array1d(0..span-1,
    [1 + sum(r in 1..incumbent_rounds)(bool2int(sum(k in 1..r)(hint_duration[k]) <= t)) | t in 0..span-1]);

constraint phase[0] = 1;
constraint forall(t in 1..span-1)(phase[t-1] <= phase[t] /\ phase[t] <= phase[t-1]+1);
constraint forall(e in 1..edges)(
  phase[hint_start[src[e]]] = phase[hint_start[dst[e]]] -> worker[src[e]] = worker[dst[e]]
);
constraint forall(t in 0..span-1, w in 1..workers)(
  sum(i in 1..n where hint_start[i] = t)(bool2int(worker[i] = w)) <= cpus[w]
);
solve :: warm_start(worker, hint_worker)
      :: warm_start(phase, hint_phase)
      minimize phase[span-1];
