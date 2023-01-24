//package othello.ai;
//
//import othello.game.Game;
//import othello.game.Move;
//import othello.game;
//
//import java.util.List;
//
//public class SmartStrategy implements Strategy {
//    @Override
//    public String getName() {
//        return "Smart";
//    }
//
//    @Override
//    public List<Move> determineMove(Game game) {
//        Move winningMove = findWinningMove(game);
//        if (winningMove != null) {
//            return winningMove;
//        }
//
//        List<Move> moves = game.getValidMoves();
//        for (Move move : moves) {
//            TicTacToeGame copiedGame = (TicTacToeGame) game.deepCopy();
//            copiedGame.doMove(move);
//            copiedGame.nextTurn();
//            Move opponentWinningMove = findWinningMove(copiedGame);
//            if (opponentWinningMove == null) {
//                return move;
//            }
//        }
//
//        int max = moves.size() - 1;
//        int min = 0;
//        int range = max - min + 1;
//        return moves.get((int) (Math.random() * range) + min);
//    }
//
//    private Move findWinningMove(Game game) {
//        List<Move> moves = game.getValidMoves();
//        for (Move move : moves) {
//            TicTacToeGame copiedGame = (TicTacToeGame) game.deepCopy();
//            copiedGame.doMove(move);
//            if (copiedGame.getWinner() == copiedGame.getTurn()) {
//                return move;
//            }
//        }
//        return null;
//    }
//}
