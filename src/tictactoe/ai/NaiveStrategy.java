package tictactoe.ai;

import tictactoe.model.Game;
import tictactoe.model.Move;

import java.util.List;

public class NaiveStrategy implements Strategy {

    @Override
    public String getName() {
        return "Naive Strategy";
    }

    @Override
    public Move determineMove(Game game) {
        List<Move> moves = game.getValidMoves();
        int max = moves.size() - 1;
        int min = 0;
        int range = max - min + 1;
        return moves.get((int) (Math.random() * range) + min);
    }
}
