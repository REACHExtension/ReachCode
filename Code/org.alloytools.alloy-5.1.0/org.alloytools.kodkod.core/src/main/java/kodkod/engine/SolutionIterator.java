package kodkod.engine;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Set;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.Options;
import kodkod.engine.fol2sat.Translation;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.satlab.SATAbortedException;
import kodkod.engine.satlab.SATSolver;
import kodkod.instance.Bounds;
import kodkod.instance.TupleSet;
import kodkod.util.ints.IntIterator;
import kodkod.util.ints.IntTreeSet;

/**
 * An iterator over all solutions of a model.
 *
 * @author Emina Torlak
 */
public final class SolutionIterator implements Iterator<Solution> {

    private Translation.Whole          translation;
    private long                       translTime;
    private int                        trivial;
    private Formula                    formula;
    private Bounds                     bounds;
    private Options                    options;
    boolean                            alternate;
    ArrayList<int[]>                   prev_solutions;
    Translation.Whole                  transl;
    boolean                            first;
    ArrayList<String>                  sig_names;
    ArrayList<String>                  extension_sig_names;
    HashMap<String,ArrayList<Integer>> sig_to_cnf;
    int                                scope_target;

    /**
     * Constructs a solution iterator for the given formula, bounds, and options.
     */
    SolutionIterator(Formula formula, Bounds bounds, Options options) {
        this.translTime = System.currentTimeMillis();
        this.translation = Translator.translate(formula, bounds, options);
        this.translTime = System.currentTimeMillis() - translTime;
        this.formula = formula;
        this.bounds = bounds;
        this.options = options;
        this.trivial = 0;
        transl = translation;
        prev_solutions = new ArrayList<int[]>();
        alternate = true;
        first = true;
    }

    @SuppressWarnings("static-access" )
    SolutionIterator(Formula formula, Bounds bounds, Options options, int scope_target, ArrayList<String> sig_names, ArrayList<String> extension_sig_names) {
        active_sig = 0;
        this.translTime = System.currentTimeMillis();
        this.translation = Translator.translate(formula, bounds, options);
        this.translTime = System.currentTimeMillis() - translTime;
        this.formula = formula;
        this.bounds = bounds;
        this.options = options;
        this.trivial = 0;
        transl = translation;
        prev_solutions = new ArrayList<int[]>();
        alternate = true;
        first = true;
        this.scope_target = scope_target;
        this.sig_names = sig_names;
        sig_to_cnf = new HashMap<String,ArrayList<Integer>>();
        this.extension_sig_names = extension_sig_names;

        for (int i = 0; i < sig_names.size(); i++) {
            ArrayList<String> temp = new ArrayList<String>();
            temp.add(sig_names.get(i));
            temp.add(sig_names.get(i) + " remainder");

            Set<Relation> name = nameToRelation(temp);

            IntTreeSet cnf_sig = new IntTreeSet();
            for (Relation rel : name) {
                cnf_sig.addAll(transl.primaryVariables(rel));
            }

            if (cnf_sig.isEmpty()) {
                if (first)
                    active_sig++;
            }

            IntIterator itr = cnf_sig.iterator();
            ArrayList<Integer> cnf_lits = new ArrayList<Integer>();
            while (itr.hasNext()) {
                //reverse list]
                int value = itr.next();
                cnf_lits.add(0, value);
            }

            sig_to_cnf.put(sig_names.get(i), cnf_lits);
        }
    }

    /**
     * Returns true if there is another solution.
     *
     * @see java.util.Iterator#hasNext()
     */
    @Override
    public boolean hasNext() {
        return translation != null;
    }

    /**
     * Returns the next solution if any.
     *
     * @see java.util.Iterator#next()
     */
    @Override
    public Solution next() {
        if (!hasNext())
            throw new NoSuchElementException();
        try {
            return translation.trivial() ? nextTrivialSolution() : nextNonTrivialSolution();
        } catch (SATAbortedException sae) {
            translation.cnf().free();
            throw new AbortedException(sae);
        }
    }

    /** @throws UnsupportedOperationException */
    @Override
    public void remove() {
        throw new UnsupportedOperationException();
    }

    /**
     * Solves {@code translation.cnf} and adds the negation of the found model to
     * the set of clauses. The latter has the effect of forcing the solver to come
     * up with the next solution or return UNSAT. If
     * {@code this.translation.cnf.solve()} is false, sets {@code this.translation}
     * to null.
     *
     * @requires this.translation != null
     * @ensures this.translation.cnf is modified to eliminate the current solution
     *          from the set of possible solutions
     * @return current solution
     */


    private Set<Relation> nameToRelation(ArrayList<String> rels) {
        Map<String,Relation> name2rel = new HashMap<>();
        for (Relation rel : bounds.relations()) {
            if (name2rel.put(rel.name(), rel) != null) {
                throw new IllegalArgumentException("Name conflict");
            }
        }
        Set<Relation> result = new HashSet<>();
        for (String r : rels) {
            result.add(name2rel.get(r));
        }
        return result;
    }

    int active_sig = 0;

    private Solution nextNonTrivialSolution() {

        final int primaryVars = transl.numPrimaryVariables();
        ArrayList<int[]> new_clauses = new ArrayList<int[]>();
        SATSolver cnf = transl.cnf();

        boolean isSat = false;
        long startSolve;
        long endSolve;
        Solution sol;
        Statistics stats = null;
        boolean unsat_twice = false;
        boolean unsat_once = false;

        boolean add_clauses = true;

        while (true) {
            if (add_clauses && active_sig < sig_names.size()) {
                for (int j = 0; j < sig_to_cnf.get(sig_names.get(active_sig)).size(); j++) {
                    int[] c = new int[1];
                    c[0] = sig_to_cnf.get(sig_names.get(active_sig)).get(j);
                    cnf.addClause(c);
                }
                add_clauses = false;
            }

            transl.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(), cnf.numberOfClauses());
            startSolve = System.currentTimeMillis();
            isSat = cnf.solve();
            endSolve = System.currentTimeMillis();
            stats = new Statistics(transl, translTime, endSolve - startSolve);

            if (isSat) {
                unsat_once = false;
                break;
            } else {
                if (unsat_once) {
                    unsat_twice = true;
                    break;
                }
                unsat_once = true;
                active_sig++;
                transl = Translator.translate(formula, bounds, options);
                cnf = transl.cnf();
                add_clauses = true;
                for (int[] prev_negation : prev_solutions) {
                    cnf.addClause(prev_negation);
                }
            }

            if (active_sig >= sig_names.size() && extension_sig_names.size() == 0) {
                break;
            }
        }

        /*
         * if (!isSat && extension_sig_names.size() > 0) {
         * transl.options().reporter().solvingCNF(primaryVars, cnf.numberOfVariables(),
         * cnf.numberOfClauses()); startSolve = System.currentTimeMillis(); isSat =
         * cnf.solve(); endSolve = System.currentTimeMillis(); add_clauses = false;
         * stats = new Statistics(transl, translTime, endSolve - startSolve); }
         */

        if (isSat) {
            // extract the current solution; can't use the sat(..) method
            // because it frees the sat solver
            sol = Solution.satisfiable(stats, transl.interpret());
            // add the negation of the current model to the solver
            //To start, keep all nodes the same

            /*
             * Stores the information to ensure the negation of the current solution is
             * accounted for.
             */
            int[] traditional = new int[primaryVars];
            for (int i = 1; i <= primaryVars; i++) {
                traditional[i - 1] = cnf.valueOf(i) ? -i : i;
            }
            prev_solutions.add(traditional);
            cnf.addClause(traditional);

        } else {
            sol = Solver.unsat(transl, stats); // this also frees up solver
            // resources, if any
            translation = null; // unsat, no more solutions
        }


        return sol;
    }

    /**
     * Returns the trivial solution corresponding to the trivial translation stored
     * in {@code this.translation}, and if {@code this.translation.cnf.solve()} is
     * true, sets {@code this.translation} to a new translation that eliminates the
     * current trivial solution from the set of possible solutions. The latter has
     * the effect of forcing either the translator or the solver to come up with the
     * next solution or return UNSAT. If {@code this.translation.cnf.solve()} is
     * false, sets {@code this.translation} to null.
     *
     * @requires this.translation != null
     * @ensures this.translation is modified to eliminate the current trivial
     *          solution from the set of possible solutions
     * @return current solution
     */
    private Solution nextTrivialSolution() {
        final Translation.Whole transl = this.translation;

        final Solution sol = Solver.trivial(transl, translTime); // this also
                                                                // frees up
                                                                // solver
                                                                // resources,
                                                                // if unsat

        if (sol.instance() == null) {
            translation = null; // unsat, no more solutions
        } else {
            trivial++;

            final Bounds bounds = transl.bounds();
            final Bounds newBounds = bounds.clone();
            final List<Formula> changes = new ArrayList<Formula>();

            for (Relation r : bounds.relations()) {
                final TupleSet lower = bounds.lowerBound(r);

                if (lower != bounds.upperBound(r)) { // r may change
                    if (lower.isEmpty()) {
                        changes.add(r.some());
                    } else {
                        final Relation rmodel = Relation.nary(r.name() + "_" + trivial, r.arity());
                        newBounds.boundExactly(rmodel, lower);
                        changes.add(r.eq(rmodel).not());
                    }
                }
            }

            // nothing can change => there can be no more solutions (besides the
            // current trivial one).
            // note that transl.formula simplifies to the constant true with
            // respect to
            // transl.bounds, and that newBounds is a superset of transl.bounds.
            // as a result, finding the next instance, if any, for
            // transl.formula.and(Formula.or(changes))
            // with respect to newBounds is equivalent to finding the next
            // instance of Formula.or(changes) alone.
            final Formula formula = changes.isEmpty() ? Formula.FALSE : Formula.or(changes);

            final long startTransl = System.currentTimeMillis();
            translation = Translator.translate(formula, newBounds, transl.options());
            translTime += System.currentTimeMillis() - startTransl;
        }
        return sol;
    }

    public void setScope(int scope) {
        scope_target = scope;
    }

    public void setSigNames(ArrayList<String> sig_names) {
        this.sig_names = sig_names;
    }
}
