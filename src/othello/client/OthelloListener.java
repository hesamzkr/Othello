package othello.client;

import othello.game.HumanPlayer;
import othello.game.Move;

import java.util.List;

public class OthelloListener implements Listener {
    public void print(String msg) {
        System.out.printf("%s%n", msg);
    }

    public void printHello(String msg) {
        print("Server responded with Hello");
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

    }

    public void printGameOverDraw() {

    }

    public void printGameOverDisconnected(String msg) {

    }

    public void printGameOverVictory(String msg) {

    }
}
