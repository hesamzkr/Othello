package othello.ai;

import othello.game.Game;
import othello.game.Move;
import othello.game.NoValidMovesException;

import java.util.List;

/**
 * Strategy of the way the player chooses
 * the move to make
 */
public interface Strategy {
    /**
     * get the name of the strategy
     *
     * @return name of the strategy
     */
    String getName();

    /**
     * Returns a legal move, given the current state
     * of the game.
     *
     * @param game the game strategy is for
     * @return a legal move
     */
    List<Move> determineMove(Game game) throws NoValidMovesException;
}
