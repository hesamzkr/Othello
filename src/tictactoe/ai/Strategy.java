package tictactoe.ai;

import tictactoe.model.Game;
import tictactoe.model.Move;

public interface Strategy {

    /**
     * get the name of the strategy
     * @return name of the strategy
     */
    //@ ensures \result != null;
    public String getName();

    /**
     * Returns a legal move, given the current state
     * of the game.
     * @param game the game strategy is for
     * @return a legal move
     */
    //@ requires game != null;
    //@ ensures game.isValidMove(\result);
    public Move determineMove(Game game);
}
