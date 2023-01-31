package othello.client;

import othello.game.HumanPlayer;
import othello.game.Mark;
import othello.game.Move;

import java.util.List;

public class OthelloListener implements Listener {

    private final OthelloClient client;

    public OthelloListener(OthelloClient client) {
        this.client = client;
    }

    public void print(String msg) {
        System.out.printf("%s%n", msg);
    }

    public void printHello(String msg) {
        print("Server responded with Hello " + msg);
    }

    public void printList(String[] names) {
        print("List of users:");
        for (int i = 1; i < names.length; i++) {
            print(String.format("%s) %s", i, names[i]));
        }
    }

    public void printOpponentSkipped() {
        print("Opponent skipped as they had no valid moves");
    }

    public void printGame() {
        printBoard();
        print(OthelloApp.IN_GAME);
    }

    public void printBoard() {
        print(client.getGame().toString());
    }

    public void printGameOverDraw() {
        print("Game is a draw!");
        print("Press ENTER to go to the main menu");
    }

    public void printGameOverDisconnected(String name) {
        print(String.format("%s won the game. opponent disconnected", name));
        print("Press ENTER to go to the main menu");
    }

    public void printGameOverVictory(String name) {
        print(String.format("Game over! %s Won", name));
        print("Press ENTER to go to the main menu");
    }

    public void printMoves() {
        List<Move> moves = client.getGame().combineMoves();
        for (int i = 0; i < moves.size(); i++) {
            print(String.format("%s) %s", i + 1, moves.get(i).getIndex()));
        }
        if (moves.isEmpty() && client.getPlayer() instanceof HumanPlayer) {
            client.pressEnter = true;
            print("You don't have any valid moves");
            print("Press ENTER to pass your turn");
        }
        if (client.getPlayer() instanceof HumanPlayer) {
            print("> hint");
        }
    }

    public void printNewGameFound(String opponentName) {
        client.pressEnter = true;
        print(String.format("Found new game with %s\nPress ENTER to proceed", opponentName));
    }
}
