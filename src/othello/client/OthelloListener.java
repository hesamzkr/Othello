package othello.client;

import othello.game.HumanPlayer;
import othello.game.Mark;
import othello.game.Move;

import java.util.List;

/**
 * Listener for the OthelloGame so that the TUI and client can interact.
 */
public class OthelloListener implements Listener {

    private final OthelloClient client;

    /**
     * Constructor which sets the client
     *
     * @param client of the listener
     */
    public OthelloListener(OthelloClient client) {
        this.client = client;
    }

    /**
     * Prints the message on to the TUI in the format specified
     *
     * @param msg to be printed
     */
    public void print(String msg) {
        System.out.printf("%s%n", msg);
    }

    /**
     * Prints response of server to the hello message
     *
     * @param msg server's message
     */
    public void printHello(String msg) {
        print("Server responded with Hello " + msg);
    }

    /**
     * Prints the list of users sent by the server
     *
     * @param names list of names sent by server
     */
    public void printList(String[] names) {
        print("List of users:");
        for (int i = 1; i < names.length; i++) {
            print(String.format("%s) %s", i, names[i]));
        }
    }

    /**
     * Print message when opponent skipped their move
     */
    public void printOpponentSkipped() {
        print("Opponent skipped as they had no valid moves");
    }

    /**
     * Prints the board and in game menu
     */
    public void printGame() {
        printBoard();
        print(OthelloApp.IN_GAME);
    }

    /**
     * Prints the board
     */
    public void printBoard() {
        print(client.getGame().toString());
    }

    /**
     * Prints the game is a draw and the "enter" message.
     */
    public void printGameOverDraw() {
        print("Game is a draw!");
        print("Press ENTER to go to the main menu");
    }

    /**
     * Prints game over and the user who won when a disconnect happens. plus the "enter" message.
     *
     * @param name of the winner
     */
    public void printGameOverDisconnected(String name) {
        print(String.format("%s won the game. opponent disconnected", name));
        print("Press ENTER to go to the main menu");
    }

    /**
     * Prints game over and the user who won when the game is over. plus the "enter" message.
     *
     * @param name of the winner
     */
    public void printGameOverVictory(String name) {
        print(String.format("Game over! %s Won", name));
        print("Press ENTER to go to the main menu");
    }

    /**
     * Prints all valid moves for player to make.
     * Adds hint to the menu if player is HumanPlayer.
     */
    public void printMoves() {
        if (client.getPlayer() instanceof HumanPlayer) {
            print("c) Hint");
        }
        List<Move> moves = client.getGame().combineMoves();
        for (int i = 0; i < moves.size(); i++) {
            print(String.format("%s) %s", i + 1, moves.get(i).getIndex()));
        }
        if (moves.isEmpty() && client.getPlayer() instanceof HumanPlayer) {
            client.pressEnter = true;
            print("You don't have any valid moves");
            print("Press ENTER to pass your turn");
        }
    }

    /**
     * Prints new game found message and sets printing enter to true.
     *
     * @param opponentName name of the opponent
     * @param mark         of the clients player
     */
    public void printNewGameFound(String opponentName, Mark mark) {
        client.pressEnter = true;
        print(String.format("Found new game with %s as %s\nPress ENTER to proceed", opponentName, mark));
    }
}
