package othello.game;

import othello.ai.Strategy;

import java.util.List;

/**
 * A player which their moves is decided by a Strategy
 */
public class ComputerPlayer extends AbstractPlayer {

    private final Strategy strategy;

    /**
     * Constructor which takes the user's name and the strategy
     *
     * @param name     of the player
     * @param strategy of the computer player to choose the moves
     */
    public ComputerPlayer(String name, Strategy strategy) {
        super(name);
        this.strategy = strategy;
    }

    /**
     * Using the strategy to determine the move of the player
     *
     * @param game the current game
     * @return the move the player has chosen
     * @throws NoValidMovesException if there are no valid moves player can make
     */
    @Override
    public List<Move> determineMove(Game game) throws NoValidMovesException {
        return strategy.determineMove(game);
    }

    /**
     * Set the mark of player
     *
     * @param m to be set for player
     */
    public void setMark(Mark m) {
        super.mark = m;
    }
}
