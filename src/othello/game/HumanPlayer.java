package othello.game;

import othello.game.AbstractPlayer;
import othello.game.Mark;
import tictactoe.model.*;

import java.util.Scanner;

public class HumanPlayer extends AbstractPlayer {

    private Mark mark;

    /**
     * Creates a new Player object.
     *
     * @param name
     */
    public HumanPlayer(String name) {
        super(name);
    }

    @Override
    public Move determineMove(Game game) {
        Scanner scan = new Scanner(System.in);
        othello.prototypeGame.model.OthelloGame newGame = (othello.prototypeGame.model.OthelloGame) game;
        Board board = newGame.getBoard();
        while (true) {
            System.out.print("Please enter a valid move: ");
            int index = scan.nextInt();
            Move newMove = new OthelloMove(newGame.getMark(), index);
            if (game.isValidMove(newMove)) {
                return newMove;
            } else {
                System.out.println("Invalid move, try again");
            }
        }
    }
}
