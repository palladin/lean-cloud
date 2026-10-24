% Offline scheduling experiment. One unit of CPU time per module.
% A (round, worker) pair is one job. Cross-job dependencies need a barrier.
include "cumulative.mzn";

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

array[1..n] of var 1..max_rounds: round;
array[1..n] of var 1..workers: worker;
array[1..n] of var 0..horizon-1: start;
array[1..max_rounds] of var 0..horizon: duration;
array[0..max_rounds] of var 0..horizon: boundary :: no_output;
var 1..max_rounds: used_rounds = max(round);
var 0..upper: cost = boundary[max_rounds] + penalty * used_rounds;

constraint boundary[0] = 0;
constraint boundary[max_rounds] >= (n + sum(cpus) - 1) div sum(cpus);
constraint forall(r in 1..max_rounds)(
  boundary[r] = boundary[r-1] + duration[r] /\
  (duration[r] > 0 <-> r <= used_rounds)
);
constraint forall(i in 1..n)(
  start[i] >= boundary[round[i]-1] /\ start[i]+1 <= boundary[round[i]] /\
  start[i] >= earliest[i] /\ start[i] + tail_length[i] <= boundary[max_rounds]
);
constraint forall(e in 1..edges)(
  start[src[e]]+1 <= start[dst[e]] /\
  round[src[e]] <= round[dst[e]] /\
  (round[src[e]] = round[dst[e]] -> worker[src[e]] = worker[dst[e]])
);
constraint forall(w in 1..workers)(
  cumulative(start, [1 | i in 1..n], [bool2int(worker[i] = w) | i in 1..n], cpus[w])
);
constraint cumulative(start, [1 | i in 1..n], [1 | i in 1..n], sum(cpus));
constraint cost <= upper;

solve :: warm_start(round, hint_round)
      :: warm_start(worker, hint_worker)
      :: warm_start(start, hint_start)
      :: warm_start(duration, hint_duration)
      minimize cost;
