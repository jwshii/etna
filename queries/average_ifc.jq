
def bin: if . < 0 then "error"
         elif . < 0.1 then 0.1
         elif . < 1 then 1
         elif . < 10 then 10
         elif . < 60 then 60
         else "timeout"
         end;

def average($workload; $strategy):
    flatten
    | map(select((.workload | test($workload)) and (.strategy | test($strategy))))
    | if ($workload == ".*") and ($strategy == ".*") then group_by(.mutant, .property, .strategy, .workload)
      elif $workload == ".*" then group_by(.mutant, .property, .workload)
      elif $strategy == ".*" then group_by(.mutant, .property, .strategy)
      else group_by(.mutant, .property)
      end
    | map({
        workload: .[0].workload,
        strategy: .[0].strategy,
        mutant: .[0].mutant,
        property: .[0].property,
        time: (map(.time) | add / length),
        passed: (map(.passed) | add / length),
        discards: (map(.discards) | add / length),
        bin: ((map(.time) | add / length) | bin)
    });

def count_bins($averages):
    $averages
    | map(.bin)
    | group_by(.)
    | map({
        bin: .[0],
        count: length
    });


def main:
    (if $ARGS.named.workload == null then ".*" else $ARGS.named.workload + "$" end) as $workload
    | (if $ARGS.named.strategy == null then ".*" else $ARGS.named.strategy + "$" end) as $strategy
    | average($workload; $strategy)
    | if $ARGS.named.bins == "true" then 
        count_bins(.)
        | sort_by(.bin)
        | map({bin: .bin, count: .count})
        | {bins: .}
     end
    ;

main