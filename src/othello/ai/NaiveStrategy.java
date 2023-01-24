package othello.ai;

import othello.game.Game;
import othello.game.Move;
import othello.game.NoValidMoves;
import othello.game.OthelloGame;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

public class NaiveStrategy implements Strategy {

    @Override
    public String getName() {
        return "Naive Strategy";
    }

    @Override
    public List<Move> determineMove(Game game) throws NoValidMoves {
        List<Move> moves = game.getValidMoves(game.getTurn().getMark());
        Random random = new Random();

        if (moves.isEmpty()) {
            throw new NoValidMoves();
        }
        List<int[]> validIndices = ((OthelloGame) game).showValids();
        int index = random.nextInt(validIndices.size());
        int row = validIndices.get(index)[0];
        int col = validIndices.get(index)[1];
        List<Move> playMoves = new ArrayList<>();
        for (Move m : moves) {
            if (m.getRow() == row && m.getCol() == col) {
                playMoves.add(m);
            }
        }
        return playMoves;
    }
}
