package othello.ai;

import othello.game.*;

import java.util.List;

/**
 * Performs the MCTS algorithm which involves selection, expansion, simulation and backpropagation in order to find the most optimal move to play.
 */
public class MonteCarloStrategy implements Strategy {

    /**
     * Represents how often MCTS should be iterated based on the selected difficulty.
     */
    private int numIterations;

    public MonteCarloStrategy(Difficulty difficulty) {
        switch (difficulty) {
            case EASY -> numIterations = 10;
            case MEDIUM -> numIterations = 1600;
            case HARD -> numIterations = 30000;
        }
    }

    @Override
    public String getName() {
        return "Monte Carlo Tree Search ";
    }

    /**
     * Determines which move to play by going through the four stages of MCTS (selection, expansion, simulation and backpropagation)
     * and iterating that a specified number of times.
     *
     * @param game the current game for which the most optimal move should be calculated for.
     * @return the most optimal move according to MCTS.
     */
    @Override
    public List<Move> determineMove(Game game) {
        Node root = new McNode(null, new State(game, null));
        for (int i = 0; i < numIterations; i++) {
            Game newGame = game.deepCopy();
            Node newNode = select(root, newGame);
            newNode = ((McNode) newNode).expandNode((OthelloGame) newGame);
            Score score = simulate(newGame);
            ((McNode) newNode).backPropagation(score);
        }

        Node childWithMostVisits = ((McNode) root).getNodeWithMostSims();
        if (childWithMostVisits.getState().moveToParent.isEmpty() || childWithMostVisits.getState().moveToParent == null) {
            System.out.println(childWithMostVisits.getState().getPlayer().getMark());
            System.out.println(childWithMostVisits.getChildArray().size());
            ((McNode) childWithMostVisits).printTree();
            System.out.println("Something very wrong is going on.");
            throw new RuntimeException("Something very wrong is going on.");
        }
        return childWithMostVisits.getState().moveToParent;
    }

    /**
     * Randomly simulates how a game plays out from a certain game-state.
     *
     * @param newGame from which the rollout should happen.
     * @return the score of the game depending on who won.
     */
    private Score simulate(Game newGame) {
        OthelloGame copy = ((OthelloGame) newGame).deepCopy();
        while (!copy.isGameOver()) {
            try {
                Mark current = copy.getTurn().getMark();
                if (copy.getValidMoves(current).isEmpty()) {
                    throw new NoValidMoves();
                }
                copy.doMove(new NaiveStrategy().determineMove(copy));
            } catch (NoValidMoves ignored) {
            }
            copy.nextTurn();
        }
        return copy.getScores();
    }

    /**
     * Select which node should be expanded next.
     *
     * @param node    the current node in the search tree.
     * @param newGame the current game state.
     * @return the selected node for expansion.
     */
    private Node select(Node node, Game newGame) {
        while (!((McNode) node).canExpandNode() && !newGame.isGameOver()) {
            node = ((McNode) node).selectNode();
            List<Move> move = ((McNode) node).getState().moveToParent;
            if (move != null && !move.isEmpty()) {
                newGame.doMove(move);
                ((OthelloGame) newGame).nextTurn();
            }
        }
        return node;
    }
}
