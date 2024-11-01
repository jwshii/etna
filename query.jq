
def abs: if . < 0 then - . else . end;
def bin: if . < 0 then -1
         elif . < 0.1 then 1
         elif . < 1 then 2
         elif . < 10 then 3
         elif . < 60 then 4
         else 5
         end;

# .[] 
# | select(has("process_time")) 
# | select(.process_time - .process_time_monotonic | abs | select(. > 0.1)) 
# | "experiments/coq-experiments/proplang/ShallowVsDeep/results/\(.workload),\(.strategy),\(.mutant),\(.property),shallow.json"

.[] 
| select(has("process_time")) 
# | select(((.process_time | bin) != (.process_time_monotonic | bin)) or ((.process_time_monotonic | bin) != (.time | bin)))
| select(((.process_time | bin) != (.process_time_monotonic | bin)))
# | select(((.process_time_monotonic | bin) != (.time | bin))) 
| "experiments/coq-experiments/proplang/ShallowVsDeep/results/\(.workload),\(.strategy),\(.mutant),\(.property),deeper.json"
# | "==> \(.workload), \(.strategy), \(.mutant), \(.property), \(.process_time_monotonic): \(.process_time_monotonic | bin), \(.time): \(.time | bin)"