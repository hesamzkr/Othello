package othello.ui;

import othello.ai.Difficulty;
import othello.ai.MonteCarloStrategy;
import othello.ai.NaiveStrategy;
import othello.client.OthelloClient;
import othello.client.Protocol;
import othello.game.*;
import othello.game.Player;

import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.List;
import java.util.Scanner;

public class OthelloTUI {
    private OthelloClient client;
    private Scanner scanner;

    private static final String MAIN_MENU = "quit"; // QUEUE LIST QUIT
    private static final String IN_QUEUE = ""; // CANCEL-QUEUE LIST QUIT
    private static final String IN_GAME = "queue"; // CHOOSE-MOVES LIST QUIT
    private static final String CHOOSE_PLAYER = "list"; // CHOOSE BETWEEN AI AND HUMAN LIST


    public OthelloTUI(OthelloClient client) {
        this.client = client;
        scanner = new Scanner(System.in);
    }

    public static void main(String[] args) {
        OthelloTUI tui = new OthelloTUI(new OthelloClient());
        tui.run();
    }

    public void run() {
        String username = connectClient();
        login(username);

        print(MAIN_MENU);
        boolean inMainMenu = true;
        while (inMainMenu) {
            Integer choice = readNextInt();
            switch (choice) {
                case 1 -> {
                    queue();
                    inMainMenu = false;
                }
                case 2 -> list();
                case 3 -> quit();
            }
        }

        print(IN_QUEUE);
        boolean inQueueMenu = true;
        while (inQueueMenu) {
            Integer choice = readNextInt();
            switch (choice) {
                case 1 -> {
                    queue();
                    inQueueMenu = false;
                }
                case 2 -> list();
                case 3 -> quit();
            }
        }

        print(client.getGame().toString());
        List<Moves> moves = printMoves();
        print(IN_GAME);
        boolean inGameMenu = true;
        while (inGameMenu) {
            String choice = readNextLine();
            switch (choice) {
                case "a" -> list();
                case "b" -> quit();
                default -> {
                    try {
                        Integer moveIndex = Integer.parseInt(choice);


                        client.sendMove(moveIndex);

                        inGameMenu = false;
                    } catch (NumberFormatException ignored) {
                        print("Enter a valid choice from the menu");
                    }
                }
            }
        }



        while (true) {
            String command = readNextLine();
            switch (command) {
                case
            }

        boolean loop = true;
        while (loop) {
            while (!game.isGameOver()) {
                System.out.println(game);
                Player player = game.getTurn();
                System.out.printf("\n%s (%s)%n", game.getTurn().toString(), game.getTurn().getMark());
                List<Move> moves = null;
                try {
                    if (game.getValidMoves(player.getMark()).isEmpty()) {
                        throw new NoValidMoves();
                    }
                    moves = player.determineMove(game);
                    game.doMove(moves);
                } catch (NoValidMoves e) {
                    System.out.printf("%s%n", e.getMessage());
                }
                game.nextTurn();
            }
            System.out.printf("\n%s\n", game);
            Player winner = game.getWinner();
            if (winner != null) {
                Mark win = winner.getMark();
                Mark other = win.other();
                System.out.printf("The winner is: %s(%s)!, final score: %s vs %s \n", winner, winner.getMark(), game.scores().get(win), game.scores().get(win.other()));
            } else {
                System.out.println("The game is a draw!");
            }
            System.out.println("Do you want to continue? yes/no?");
            Scanner scan = new Scanner(System.in);
            String args = scan.nextLine();
            switch (args) {
                case "yes":
                    Player current = game.getTurn();
                    game.nextTurn();
                    Player next = game.getTurn();
                    game = new OthelloGame(current, next);
                    break;
                case "no":
                    loop = false;
                    break;
                default:
                    System.out.println("Unknown command");
            }
        }
    }
    }

    private static Player createPlayer(String name) {
        switch (name) {
            case "-N":
                return new ComputerPlayer(new NaiveStrategy());
//            case "-S":
//                return new ComputerPlayer(mark, new SmartStrategy());
            case "-M":
                return new ComputerPlayer(new MonteCarloStrategy(selectDifficulty(new Scanner(System.in))));
            default:
                return new HumanPlayer(name);
        }
    }

    private static Difficulty selectDifficulty(Scanner scanner) {
        System.out.println("Select a difficulty: easy, mid (medium), hard");
        String setting = scanner.nextLine();
        while (true) {
            switch (setting) {
                case "easy":
                    return Difficulty.EASY;
                case "mid":
                    return Difficulty.MEDIUM;
                case "hard":
                    return Difficulty.HARD;
                default:
                    System.out.println("Select a valid difficulty.");
            }
        }
    }

    private String connectClient() {
        while (true) {
            try {
                print("Enter the server's address:");
                String address = readNextLine();
                print("Enter the port to connect to:");
                Integer port = readNextInt();
                client.connect(InetAddress.getByName(address), port);
                print("Connected to the server");
                print("Enter your username");
                String username = readNextLine();
                client.send(Protocol.sendHelloClient(username));
                return username;
            } catch (UnknownHostException ignored) {
                print("Cannot connect to the server with specified port");
            }
        }
    }

    private void login(String username) {
        while (true) {
            client.send(Protocol.sendLogin(username));
            if (client.getLoggedIn()) {
                client.setUsername(username);
                break;
            }
            print("Choose a different username");
            username = readNextLine();
        }

    }

    private void print(String msg) {
        System.out.printf("%s%n", msg);
    }

    public void printMoves() {

    }

    public String readNextLine() {
        while (true) {
            String text = scanner.nextLine();
            if (!text.isEmpty()) {
                return text;
            }
        }
    }

    public Integer readNextInt() {
        while (true) {
            try {
                String text = scanner.nextLine();
                if (text.isEmpty()) {
                    continue;
                }
                return Integer.parseInt(text);
            } catch (NumberFormatException ignored) {
            }
        }
    }
}
