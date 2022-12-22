package tictactoe.ai;

import tictactoe.model.AbstractPlayer;
import tictactoe.model.Game;
import tictactoe.model.Mark;
import tictactoe.model.Move;

public class ComputerPlayer extends AbstractPlayer {

    private Strategy strategy;

    /**
     * Creates a new Player object.
     *
     * @param mark and strategy
     */
    public ComputerPlayer(Mark mark, Strategy strategy) {
        super(String.format("%s-%s", strategy.getName(), mark));
        this.strategy = strategy;
    }

    @Override
    public Move determineMove(Game game) {
        return strategy.determineMove(game);
    }

    public Strategy getStrategy() {
        return strategy;
    }

    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
    }
}
