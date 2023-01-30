package othello.game;

import java.util.ArrayList;
import java.util.List;
import java.util.Scanner;

public class HumanPlayer extends AbstractPlayer {

    public HumanPlayer(String name) {
        super(name);
    }

    @Override
    public List<Move> determineMove(Game game) throws NoValidMoves {
        Scanner scan = new Scanner(System.in);
        while (true) {
            List<Move> playMoves = new ArrayList<>();
            System.out.print("Please enter a valid move: ");
            int index = scan.nextInt();
            int row = index / Board.DIM;
            int col = index % Board.DIM;
            List<Move> moves = game.getValidMoves(super.mark);
            if (moves.isEmpty()) {
                throw new NoValidMoves();
            }
            for (Move m : moves) {
                if (m.getRow() == row && m.getCol() == col) {
                    playMoves.add(m);
                }
            }
            if (!playMoves.isEmpty()) {
                return playMoves;
            } else {
                System.out.println("Invalid move entered.");
            }
        }
    }

    public void setMark(Mark m) { //Clean: is this useless?
        super.mark = m;
    }
}
