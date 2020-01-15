import matplotlib
matplotlib.use('Agg')
import json
import numpy as np
import matplotlib.pyplot as plt

with open("results2.json", "r") as fh:
    d = json.load(fh)
    fileSizes = [int(s)/1000.0 for s in d["file_sizes"]]
    lexerTimes = [float(s) for s in d["lexer_times"]]
    parserTimes = [float(s) for s in d["parser_times"]]

print fileSizes
print lexerTimes
print parserTimes

N = len(fileSizes)

ind = np.arange(N)    # the x locations for the groups
width = 20       # the width of the bars: can also be len(x) sequence

plt.figure(figsize=(13.5, 5))

# p1 = plt.bar(fileSizes, menhirParserTimes, width)
p2 = plt.bar([fs + width for fs in fileSizes], lexerTimes, width)
p3 = plt.bar([fs + width for fs in fileSizes], parserTimes, width, bottom = lexerTimes)

"""
p2 = plt.bar(ind + width, menhirTokenizerTimes, width)
p3 = plt.bar(ind + width, menhirParserTimes, width, bottom = menhirTokenizerTimes)
"""
plt.xlabel("File Size (KB)")
plt.ylabel("Time (s)")

#plt.xticks(fileSizes, [str(fs) for fs in fileSizes])
plt.legend((p2[0], p3[0]), ("Menhir Tokenizer", "All(*) Parser"))
"""plt.yticks(np.arange(0, 81, 10))
plt.legend((p1[0], p2[0]), ('Men', 'Women'))
"""
plt.savefig("JSON_parser_evaluation.eps", format="eps", dpi=1000)
