import java.io.*;
import java.util.*;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.tree.*;
import org.antlr.v4.tool.*;
import org.json.*;

public class BenchmarkANTLR {

    enum Benchmark { JSON, XML, DOT, PYTHON }

    static String JSON_GRAMMAR        = "JSON.g4";
    static String JSON_START_SYM      = "json";

    static String DOT_GRAMMAR         = "DOT.g4";
    static String DOT_START_SYM       = "graph";

    static String PYTHON_GRAMMAR      = "Python3.g4";
    static String PYTHON_START_SYM    = "file_input";

    static String XML_LEXER_GRAMMAR   = "XMLLexer.g4";
    static String XML_PARSER_GRAMMAR  = "XMLParser.g4";
    static String XML_START_SYM       = "document";

    static int THROWAWAY_TRIALS       = 2;
    static int RECORDED_TRIALS        = 5;

    public static CommonTokenStream getTokenStream(Benchmark benchmark, String dataFile) throws IOException {
	CharStream stream = CharStreams.fromFileName(dataFile);
	Lexer lexer;
	switch (benchmark) {
	  case JSON :
	      lexer = new JSONLexer(stream);
	      break;
	  case XML :
	      lexer = new XMLLexer(stream);
	      break;
  	  case DOT :
	      lexer = new DOTLexer(stream);
	      break;
	  case PYTHON :
	      lexer = new Python3Lexer(stream);
	      break;
	  default :
	      throw new RuntimeException("unrecognized benchmark value");
	}
	return new CommonTokenStream(lexer);
    }

    public static ParserInterpreter getInterp(Benchmark benchmark, CommonTokenStream tokens) throws IOException {
	Grammar g;
	switch (benchmark) {
	  case JSON :
	      g = Grammar.load(JSON_GRAMMAR);
	      break;
	  case XML :
	      g = Grammar.load(XML_PARSER_GRAMMAR);
	      break;
  	  case DOT :
	      g = Grammar.load(DOT_GRAMMAR);
	      break;
	  case PYTHON :
	      g = Grammar.load(PYTHON_GRAMMAR);
	      break;
	  default :
	      throw new RuntimeException("unrecognized benchmark value");
	}
	return g.createParserInterpreter(tokens);
    }

    public static String getStartSymbol(Benchmark benchmark) throws IOException {
	switch (benchmark) {
	  case JSON :
	      return JSON_START_SYM;
	  case XML :
	      return XML_START_SYM;
  	  case DOT :
	      return DOT_START_SYM;
	  case PYTHON :
	      return PYTHON_START_SYM;
	  default :
	      throw new RuntimeException("unrecognized benchmark value");
	}
    }

    public static int getNumTokens(Benchmark benchmark, String dataFile) throws IOException {
	CommonTokenStream tokenStream = getTokenStream(benchmark, dataFile);
	tokenStream.fill();
	return tokenStream.getTokens().size();
    }

    public static JSONArray runInterpTrials(Benchmark benchmark,
					    String dataFile,
					    boolean preTokenize) throws IOException {
	List<Double> times = new ArrayList<Double>();
	for (int i = 0; i < (THROWAWAY_TRIALS + RECORDED_TRIALS); i++) {
	    CommonTokenStream tokens = getTokenStream(benchmark, dataFile);
	    if (preTokenize) {
		tokens.fill();
	    }
	    ParserInterpreter parser = getInterp(benchmark, tokens);
	    String startSymbol = getStartSymbol(benchmark);
	    long start = System.currentTimeMillis();
	    ParseTree t = parser.parse(parser.getRuleIndex(startSymbol));
	    long stop = System.currentTimeMillis();
	    if (i >= THROWAWAY_TRIALS) {
		times.add((stop - start) / 1000.0); // convert to seconds
	    }
	}
	return new JSONArray(times);
    }
    
    public static JSONObject benchmarkInterpOnFile(Benchmark benchmark,
						   String dataDir,
						   String dataFileName,
						   boolean preTokenize) throws IOException {
	String dataFile = dataDir + "/" + dataFileName;
	int numTokens = getNumTokens(benchmark, dataFile);
	JSONArray times = runInterpTrials(benchmark, dataFile, preTokenize);
	return new JSONObject().put("filename", dataFileName)
	                       .put("num_tokens", numTokens)
	                       .put("parse_times", times);
    }
    
    public static JSONArray benchmarkInterpOnDataSet(Benchmark benchmark,
						     String dataDirName,
						     boolean preTokenize) throws IOException {
	List<JSONObject> records = new ArrayList<JSONObject>();
	File dataDir = new File(dataDirName);
	List<String> dataFileNames = new ArrayList<String>(Arrays.asList(dataDir.list()));
	for (String dataFileName : dataFileNames) {
	    JSONObject record = benchmarkInterpOnFile(benchmark, dataDirName, dataFileName, preTokenize);
	    System.out.println(record.toString(4));
	    records.add(record);
	}
	// Sort the records by number of tokens
	records.sort((r1, r2) ->
		     Integer.valueOf(r1.getInt("num_tokens")).compareTo(Integer.valueOf(r2.getInt("num_tokens"))));
	return new JSONArray(records);
    }

    public static void writeResults(JSONArray benchmarkResults, String outFileName) throws Exception {
	PrintWriter writer = new PrintWriter(outFileName, "UTF-8");
	writer.print(benchmarkResults.toString(4));
	writer.close();
    }

    public static void main(String[] args) throws Exception {

	String benchmarkName = args[0];
	String dataDirName   = args[1];
	boolean preTokenize  = Boolean.parseBoolean(args[2]);
	String outFileName   = args[3];

	Benchmark benchmark;
	switch (benchmarkName) {
	  case "json" :
	      benchmark = Benchmark.JSON;
	      break;
	  case "xml" :
	      benchmark = Benchmark.XML;
	      break;
	  case "dot" :
	      benchmark = Benchmark.DOT;
	      break;
	  case "python" :
	      benchmark = Benchmark.PYTHON;
	      break;
	  default:
	      throw new RuntimeException("invalid benchmark name");
	}
	
	JSONArray records = benchmarkInterpOnDataSet(benchmark, dataDirName, preTokenize);
	writeResults(records, outFileName);
    }
}
