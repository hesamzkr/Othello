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

//    @Override
//    public List<Move> determineMove(Game game) throws NoValidMoves {
//        List<Move> moves = game.getValidMoves(game.getTurn().getMark());
//        Random random = new Random();
//
//        if (moves.isEmpty()) {
//            throw new NoValidMoves();
//        }
//        List<int[]> validIndices = ((OthelloGame) game).showValids(moves);
//        int index = random.nextInt(validIndices.size());
//        int row = validIndices.get(index)[0];
//        int col = validIndices.get(index)[1];
//        List<Move> playMoves = new ArrayList<>();
//        for (Move m : moves) {
//            if (m.getRow() == row && m.getCol() == col) {
//                playMoves.add(m);
//            }
//        }
//        return playMoves;
//    }

    public List<Move> determineMove(Game game) throws NoValidMoves {
        List<Move> moves = game.getValidMoves(game.getTurn().getMark());
        Random random = new Random();

        if (moves.isEmpty()) {
            throw new NoValidMoves();
        }
        List<int[]> validIndices = ((OthelloGame) game).showValids(moves);
        int row;
        int col;

        int index = random.nextInt(validIndices.size());
        row = validIndices.get(index)[0];
        col = validIndices.get(index)[1];

        for (int[] i : validIndices) {
            if ((i[0] == 0 && i[1] == 0) || (i[0] == 0 && i[1] == 7) || (i[0] == 7 && i[1] == 0) || (i[0] == 7 && i[1] == 7)) {
                row = i[0];
                col = i[1];
            }
        }

        List<Move> playMoves = new ArrayList<>();
        for (Move m : moves) {
            if (m.getRow() == row && m.getCol() == col) {
                playMoves.add(m);
            }
        }
        return playMoves;
    }
}
