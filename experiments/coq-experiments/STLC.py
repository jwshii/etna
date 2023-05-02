import os

from benchtool.Coq import Coq
from benchtool.Plot import all_results, create_df, generate_dashboard
from benchtool.Types import TrialConfig, ReplaceLevel, LogLevel

RESULTS = f'{os.getcwd()}/results/Coq/STLC'

tool = Coq(results=RESULTS, log_level=LogLevel.DEBUG, replace_level=ReplaceLevel.REPLACE)
do_bench, do_plot = tool.parse_args()

if do_bench:
    bench = next(bench for bench in tool.all_benches() if bench.name == 'STLC')
    tool._preprocess(bench)
    for variant in tool.all_variants(bench):
        run_trial = tool.apply_variant(bench, variant, no_base=True)
        for property in tool.all_properties(bench):
            for method in (method for method in tool.all_methods(bench) if method.name == "BespokeGenerator"):
                cfg = TrialConfig(bench=bench,
                                method=method.name,
                                label=method.name,
                                property="test_" + property,
                                trials=10,
                                timeout=5)
                run_trial(cfg)

if do_plot:
    df = create_df(all_results(RESULTS))
    generate_dashboard(df).run_server(debug=False)

