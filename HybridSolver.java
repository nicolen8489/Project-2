import org.sat4j.specs.ISolver;
import org.sat4j.minisat.core.Solver;
import org.sat4j.minisat.orders.VarOrderHeap;
import org.sat4j.reader.Reader;
import org.sat4j.reader.DimacsReader;
import org.sat4j.specs.IProblem;
import org.sat4j.minisat.SolverFactory;
import org.sat4j.specs.TimeoutException;
import org.sat4j.reader.ParseFormatException;
import org.sat4j.specs.ContradictionException;

import java.io.FileNotFoundException;
import java.io.IOException;

public class HybridSolver {
  public static void main(String[] args) {
    if (args.length > 0) {
      ISolver solver = SolverFactory.newDefault();
      PartialAssignmentTracing tracing = new PartialAssignmentTracing();
      solver.setSearchListener(tracing);
      ((Solver)solver).setOrder(new HybridVarOrderHeap(((VarOrderHeap)((Solver)solver).getOrder()).getPhaseSelectionStrategy(), tracing, args[0]));
      Reader reader = new DimacsReader(solver);
      IProblem problem = null;
      try {
        problem = reader.parseInstance(args[0]);
        if (problem.isSatisfiable()) {
          System.out.println("SAT");
        } else {
          System.out.println("UNSAT");
        }
      } catch (FileNotFoundException e) {
        e.printStackTrace();
      } catch (TimeoutException e) {
        e.printStackTrace();
      } catch (ParseFormatException e) {
        e.printStackTrace();
      } catch (IOException e) {
        e.printStackTrace();
      } catch (ContradictionException e) {
        e.printStackTrace();
      }
    }
  }
}
