//package othello.prototypeGame.model;
//
//import tictactoe.HumanPlayer;
//
//import java.util.ArrayList;
//import java.util.List;
//import java.util.Random;
//
//public class OthelloGame implements Game {
//
//    private Player player1;
//    private Player player2;
//    private Board board;
//    private Player turn;
//
//    public OthelloGame(Player player1, Player player2) {
//        this.player1 = player1;
//        this.player2 = player2;
//        Randomize();
//        getFirstTurn();
//        this.board = new Board();
//    }
//
//    /**
//     * should generate 0 or 1 and assign a player pattern to that
//     *
//     * @return
//     */
//    public void Randomize() {
//        HumanPlayer player1 = (HumanPlayer) this.player1;
//        HumanPlayer player2 = (HumanPlayer) this.player2;
//        Random rand = new Random();
//        int i = rand.nextInt(0, 1);
//        if (i == 0) {
//            player1.setMark(Mark.BLACK);
//            player2.setMark(Mark.WHITE);
//        } else {
//            player1.setMark(Mark.WHITE);
//            player2.setMark(Mark.BLACK);
//        }
//    }
//
//    public boolean isGameover() {
//        return board.gameOver();
//    }
//
//    /**
//     * assigns the turn to whoever has BB as their assigned Mark
//     */
//    public void getFirstTurn() {
//        if (((HumanPlayer) player1).getMark() == Mark.BLACK) {
//            turn = player1;
//        } else {
//            turn = player2;
//        }
//    }
//
//    public Player getTurn() {
//        return turn;
//    }
//
//    public Mark getMark() {
//        if (turn == player1) {
//            return Mark.BLACK;
//        } else {
//            return Mark.WHITE;
//        }
//    }
//
//    public Player getPlayerForMark(Mark m) {
//        if (((HumanPlayer) player1).getMark() == m) {
//            return player1;
//        } else {
//            return player1;
//        }
//    }
//
//    public Player getWinner() {
//        if (board.hasWinner()) {
//            if (board.isWinner(Mark.BLACK)) {
//                return getPlayerForMark(Mark.BLACK);
//            } else if (board.isWinner(Mark.WHITE)) {
//                return getPlayerForMark(Mark.WHITE);
//            }
//        }
//        return null;
//    }
//
//    /**
//     * has to check if a move is flippable
//     * check if there is a similar mark closeby
//     * check row, check column, check diagonal
//     *
//     * @return
//     */
//    public List<Move> getValidMoves(Mark m) {
//        //Map validMoves = new HashMap<Move,Move>();
//        List<Move> validMoves = new ArrayList<>();
//        if (isGameover())
//            return validMoves;
//
//        for (int row = 0; row < Board.DIM; row++) {
//            for (int col = 0; col < Board.DIM; col++) {
//                if (board.getField(row, col) == m) {
//                    Move move = new OthelloMove(m, row, col);
//                    if (board.HasLeftUpperDiagPiece(row, col, m)) {
//                        //validMoves.add(ScanUpperDiagLeft(m,row,col)); //what happens if you add null to a list??
//                        ((OthelloMove) move).addToFlip(ScanUpperDiagLeft(m, row, col));
//                    }
//                    if (board.HasRightUpperDiagPiece(row, col, m)) {
//                        //validMoves.add(ScanUpperDiagRight(m,row,col)); //what happens if you add null to a list??
//                        ((OthelloMove) move).addToFlip(ScanUpperDiagRight(m, row, col));
//                    }
//                    if (board.HasUpperPiece(row, col, m)) {
//                        //validMoves.add(ScanUpper(m,row,col)); //what happens if you add null to a list??
//                        ((OthelloMove) move).addToFlip(ScanUpper(m, row, col));
//                    }
//                    if (board.HasLeftPiece(row, col, m)) {
//                        //validMoves.add(ScanLeftPiece(m,row,col)); //what happens if you add null to a list??
//                        ((OthelloMove) move).addToFlip(ScanLeftPiece(m, row, col));
//                    }
//                    if (board.HasRightPiece(row, col, m)) {
//                        //validMoves.add(ScanRightPiece(m,row,col)); //what happens if you add null to a list??
//                        ((OthelloMove) move).addToFlip(ScanRightPiece(m, row, col));
//                    }
//                    if (board.HasLeftLowerDiagPiece(row, col, m)) {
//                        //validMoves.add(ScanLowerDiagLeft(m,row,col)); //what happens if you add null to a list??
//                        ((OthelloMove) move).addToFlip(ScanLowerDiagLeft(m, row, col));
//                    }
//                    if (board.HasLowerPiece(row, col, m)) {
//                        //validMoves.add(ScanLower(m,row,col)); //what happens if you add null to a list??
//                        ((OthelloMove) move).addToFlip(ScanLower(m, row, col));
//                    }
//                    if (board.HasRightLowerDiagPiece(row, col, m)) {
//                        //validMoves.add(ScanLowerDiagRight(m,row,col)); //what happens if you add null to a list??
//                        ((OthelloMove) move).addToFlip(ScanLowerDiagRight(m, row, col));
//                    }
//                }
//            }
//        }
//
//        return validMoves;
//    }
//
//    /**
//     * requires that HasUpperDiagLeft is true and only run in that case
//     * checks next, next piece from the current location
//     *
//     * @return
//     */
//    public ArrayList ScanUpperDiagLeft(Mark m, int row, int col) {
//        ArrayList toFlip = new ArrayList();
//        toFlip.add(new OthelloMove(m, row - 1, col - 1));
//        int checkRow = row - 2;
//        int checkCol = col - 2;
//        //Move move = new OthelloMove(m, checkRow, checkCol);
//        //((OthelloMove)move).setToFlip(new OthelloMove(m,row-1,col-1));
//        while (board.isField(checkRow, checkCol)) {
//            if (board.getField(checkRow, checkCol) == Mark.EMPTY) {
//                //((OthelloMove)move).setLinkedMark(new OthelloMove(m,row,col));
//                OthelloMove move = new OthelloMove(m, checkRow, checkCol);
//                move.addToFlip(toFlip);
//                return move;
//                //return move;
//                return toFlip;
//            } else if (board.getField(checkRow, checkCol) == m.other()) {
//                //((OthelloMove)move).setToFlip(new OthelloMove(m,checkRow,checkCol));
//                toFlip.add(new OthelloMove(m, checkRow, checkCol));
//                checkRow -= 1;
//                checkCol -= 1;
//            } else {
//                break;
//            }
//        }
//        return null;
//    }
//
//    /**
//     * Using setfield is supposed to take the location of a mark (from for loop)
//     * and then the new move (has the mark of the player) is linked to that move
//     * which allows the game to find where that mark is.
//     *
//     * @param m
//     * @param row
//     * @param col
//     * @return
//     */
//    public ArrayList ScanUpper(Mark m, int row, int col) {
//        ArrayList toFlip = new ArrayList();
//        toFlip.add(new OthelloMove(m, row - 1, col));
//        //Move move = new OthelloMove(m, checkRow, col);
//        int checkRow = row - 2;
//        while (board.isField(checkRow, col)) {
//            if (board.getField(checkRow, col) == Mark.EMPTY) {
//                //((OthelloMove)move).setLinkedMark(new OthelloMove(m,row,col));
//                return toFlip;
//            } else if (board.getField(checkRow, col) == m.other()) {
//                toFlip.add(new OthelloMove(m, row, checkRow));
//                checkRow -= 1;
//            } else {
//                break;
//            }
//        }
//        return null;
//    }
//
//    public ArrayList ScanUpperDiagRight(Mark m, int row, int col) {
//        ArrayList toFlip = new ArrayList();
//        toFlip.add(new OthelloMove(m, row - 1, col + 1));
//        int checkRow = row - 2;
//        int checkCol = col + 2;
//        while (board.isField(checkRow, checkCol)) {
//            if (board.getField(checkRow, checkCol) == Mark.EMPTY) {
//                //Move move = new OthelloMove(m, checkRow, checkCol);
//                return toFlip;
//            } else if (board.getField(checkRow, checkCol) == m.other()) {
//                toFlip.add(new OthelloMove(m, checkRow, checkCol));
//                checkRow -= 1;
//                checkCol += 1;
//            } else {
//                break;
//            }
//        }
//        return null;
//    }
//
//    public ArrayList ScanLeftPiece(Mark m, int row, int col) {
//        ArrayList toFlip = new ArrayList();
//        toFlip.add(new OthelloMove(m, row, col - 1));
//        int checkCol = col - 2;
//        while (board.isField(row, checkCol)) {
//            if (board.getField(row, checkCol) == Mark.EMPTY) {
//                //Move move = new OthelloMove(m, row, checkCol);
//                return toFlip;
//            } else if (board.getField(row, checkCol) == m.other()) {
//                toFlip.add(new OthelloMove(m, row, col));
//                checkCol -= 1;
//            } else {
//                break;
//            }
//        }
//        return null;
//    }
//
//
//    public ArrayList ScanRightPiece(Mark m, int row, int col) {
//        ArrayList toFlip = new ArrayList();
//        toFlip.add(new OthelloMove(m, row, col + 1));
//        int checkCol = col + 2;
//        while (board.isField(row, checkCol)) {
//            if (board.getField(row, checkCol) == Mark.EMPTY) {
//                Move move = new OthelloMove(m, row, checkCol);
//                return toFlip;
//            } else if (board.getField(row, checkCol) == m.other()) {
//                toFlip.add(new OthelloMove(m, row, checkCol));
//                checkCol += 1;
//            } else {
//                break;
//            }
//        }
//        return null;
//    }
//
//    public ArrayList ScanLowerDiagLeft(Mark m, int row, int col) {
//        ArrayList toFlip = new ArrayList();
//        toFlip.add(new OthelloMove(m, row + 1, col - 1));
//        int checkRow = row + 2;
//        int checkCol = col - 2;
//        while (board.isField(checkRow, checkCol)) {
//            if (board.getField(checkRow, checkCol) == Mark.EMPTY) {
//                Move move = new OthelloMove(m, checkRow, checkCol);
//                return toFlip;
//            } else if (board.getField(checkRow, checkCol) == m.other()) {
//                toFlip.add(new OthelloMove(m, checkRow, checkCol));
//                checkRow += 1;
//                checkCol -= 1;
//            } else {
//                break;
//            }
//        }
//        return null;
//    }
//
//    public ArrayList ScanLowerDiagRight(Mark m, int row, int col) {
//        ArrayList toFlip = new ArrayList();
//        toFlip.add(new OthelloMove(m, row + 1, col + 1));
//        int checkRow = row + 2;
//        int checkCol = col + 2;
//        while (board.isField(checkRow, checkCol)) {
//            if (board.getField(checkRow, checkCol) == Mark.EMPTY) {
//                //Move move = new OthelloMove(m, checkRow, checkCol);
//                return toFlip;
//            } else if (board.getField(checkRow, checkCol) == m.other()) {
//                toFlip.add(new OthelloMove(m, checkRow, checkCol));
//                checkRow += 1;
//                checkCol += 1;
//            } else {
//                break;
//            }
//        }
//        return null;
//    }
//
//    public ArrayList ScanLower(Mark m, int row, int col) {
//        ArrayList toFlip = new ArrayList();
//        toFlip.add(new OthelloMove(m, row + 1, col));
//        int checkRow = row + 2;
//        while (board.isField(checkRow, col)) {
//            if (board.getField(checkRow, col) == Mark.EMPTY) {
//                Move move = new OthelloMove(m, checkRow, col);
//                return toFlip;
//            } else if (board.getField(checkRow, col) == m.other()) {
//                toFlip.add(new OthelloMove(m, row, checkRow));
//                checkRow += 1;
//            } else {
//                break;
//            }
//        }
//        return null;
//    }
//
//
////    public boolean isValidMove(Move move) {
////        OthelloMove newMove = (OthelloMove) move;
////        if (board.isEmptyField(newMove.getIndex())) {
////            return turn == player1 && newMove.getMark() == Mark.XX || turn == player2 && newMove.getMark() == Mark.OO;
////        }
////        return false;
////    }
//
//    /**
//     * should check the move and the current turn
//     *
//     * @param move the move to check
//     * @return
//     */
//    public boolean isValidMove(Move move) {
//        OthelloMove newMove = (OthelloMove) move;
//
//        if (board.isEmptyField(newMove.getIndex())) {
//            return turn == player1 && newMove.getMark() == Mark.XX || turn == player2 && newMove.getMark() == Mark.OO;
//        }
//        return false;
//    }
//
//    /**
//     * should take a move and flip all the pieces
//     *
//     * @param move the move to play
//     */
//    public void doMove(Move move) {
//        if (move instanceof TicTacToeMove newMove) {
//            board.setField(newMove.getRow(), newMove.getColumn(), newMove.getMark());
//        }
//    }
//
//    public void nextTurn() {
//        if (turn == player1) {
//            turn = player2;
//        } else {
//            turn = player1;
//        }
//    }
//
//    public Board getBoard() {
//        return board;
//    }
//
//    public void setBoard(Board board) {
//        this.board = board;
//    }
//
//    public String toString() {
//        return board.toString();
//    }
//
//    public OthelloGame deepCopy() {
//        OthelloGame game = new OthelloGame(player1, player2);
//        if (turn != player1)
//            game.nextTurn();
//        game.setBoard(board.deepCopy());
//        return game;
//    }
//}
