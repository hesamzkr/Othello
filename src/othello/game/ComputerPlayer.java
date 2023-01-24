package othello.game;

import othello.ai.Strategy;

import java.util.List;

public class ComputerPlayer extends AbstractPlayer {

    private final Strategy strategy;

    public ComputerPlayer(Strategy strategy) {
        super(strategy.getName());
        this.strategy = strategy;
    }

    @Override
    public List<Move> determineMove(Game game) throws NoValidMoves {
        return strategy.determineMove(game);
    }

    public void setMark(Mark m) {
        super.mark = m;
    }
}
