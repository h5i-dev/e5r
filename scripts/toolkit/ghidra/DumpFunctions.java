/* Write every function Ghidra recovered, one entry point per line, to the file
 * named by the first script argument.
 *
 * analyzeHeadless has no built-in way to report what an analysis found, and
 * parsing the log would count log lines rather than functions. A post-script
 * runs inside the same JVM after analysis, so it reports the program state the
 * analysis actually produced.
 *
 * The first line is "# imagebase <hex>", because Ghidra relocates a shared
 * object to an image base of its own choosing and the caller has to undo that
 * before comparing addresses with anyone else. Every line after it is
 * "<hex entry> <isExternal> <isThunk> <name>". The caller decides what to
 * count; this script decides nothing.
 */
//@category Benchmark
import ghidra.app.script.GhidraScript;
import ghidra.program.model.listing.Function;
import ghidra.program.model.listing.FunctionIterator;

import java.io.PrintWriter;

public class DumpFunctions extends GhidraScript {
    @Override
    public void run() throws Exception {
        String[] args = getScriptArgs();
        if (args.length < 1) {
            println("DumpFunctions: no output path given");
            return;
        }
        PrintWriter out = new PrintWriter(args[0]);
        try {
            out.printf("# imagebase %s%n", currentProgram.getImageBase().toString());
            FunctionIterator it = currentProgram.getFunctionManager().getFunctions(true);
            while (it.hasNext()) {
                Function f = it.next();
                out.printf(
                    "%s %b %b %s%n",
                    f.getEntryPoint().toString(),
                    f.isExternal(),
                    f.isThunk(),
                    f.getName());
            }
        } finally {
            out.close();
        }
    }
}
