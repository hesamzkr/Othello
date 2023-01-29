package othello.server;

import othello.server.InvalidPortException;

import java.util.Scanner;

public class OthelloServerApp {
    private OthelloServer server;

    public static void main(String[] args) {
        OthelloServerApp app = new OthelloServerApp();
        app.createServer();
        app.runTui();
    }

    private void createServer() {
        Scanner scan = new Scanner(System.in);
        while (true) {
            try {
                System.out.println("Please enter a valid port number 0-65536");
                int port = scan.nextInt();
                if (port < 0 || port > 65536) {
                    throw new InvalidPortException("Invalid port entered.");
                }
                server = new OthelloServer(port);
                server.start();
                System.out.printf("Created a server at: %s%n", port);
                break;
            } catch (InvalidPortException e) {
                System.out.println(e.getMessage());
            }
        }
    }

    private void runTui() {
        Scanner scan = new Scanner(System.in);
        while (true) {
            String arg = scan.nextLine();
            switch (arg) {
                case "quit" -> {
                    server.stop();
                    return;
                }
                case "port" -> {
                    System.out.println(server.getPort());
                }
                case "address" -> {
                    System.out.println(server.getAddress());
                }
                default -> {
                    System.out.println("invalid command");
                }
            }
        }
    }
}
