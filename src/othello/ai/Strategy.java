package othello.ai;

import othello.game.Game;
import othello.game.Move;
import othello.game.NoValidMoves;

import java.util.List;

public interface Strategy {

    /**
     * get the name of the strategy
     *
     * @return name of the strategy
     */
    //@ ensures \result != null;
    public String getName();

    /**
     * Returns a legal move, given the current state
     * of the game.
     *
     * @param game the game strategy is for
     * @return a legal move
     */
    //@ requires game != null;
    //@ ensures game.isValidMove(\result);
    public List<Move> determineMove(Game game) throws NoValidMoves;
}
