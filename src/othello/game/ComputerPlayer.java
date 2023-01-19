package othello.game;

import othello.ai.Strategy;
import othello.game.AbstractPlayer;
import othello.game.Game;
import othello.game.Mark;
import othello.game.Move;

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
