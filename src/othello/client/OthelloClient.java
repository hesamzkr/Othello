package othello.client;

import othello.game.*;

import java.io.*;
import java.net.InetAddress;
import java.net.Socket;

public class OthelloClient implements Client, Runnable {

    private Socket socket;
    private Thread thread;
    private OthelloListener listener = new OthelloListener();
    private BufferedWriter bw;
    private String username;
    private Player player;
    private OthelloGame game;
    private boolean hasLoggedIn = false;

    public boolean connect(InetAddress address, int port) {
        try {
            socket = new Socket(address, port);
            bw = new BufferedWriter(new OutputStreamWriter(socket.getOutputStream()));
            thread = new Thread(this);
            thread.start();
            return true;
        } catch (IOException e) {
            return false;
        }
    }

    public void run() {
        try (BufferedReader br = new BufferedReader(new InputStreamReader(socket.getInputStream()))) {
            while (!socket.isClosed()) {
                String line;
                while ((line = br.readLine()) != null) {
                    String[] protocolSplit = line.split(Protocol.SEPARATOR);
                    switch (protocolSplit[0]) {
                        case Protocol.HELLO -> listener.printHello(protocolSplit[1]);
                        case Protocol.LOGIN -> hasLoggedIn = true;

                        case Protocol.LIST -> listener.printList(protocolSplit);

                        case Protocol.NEWGAME -> {
                            if (protocolSplit[1].equals(player.getName())) {
                                game = new OthelloGame(player, new HumanPlayer(protocolSplit[2]));
                            } else {
                                game = new OthelloGame(new HumanPlayer(protocolSplit[1]), player);
                            }
                            OthelloApp.newGameFound();
                        }
                        case Protocol.MOVE -> {
                            try {
                                int moveIndex = Integer.parseInt(protocolSplit[1]);
                                if (moveIndex == 64) {
                                    listener.printOpponentSkipped();
                                } else {
                                    game.doMove(moveIndex);
                                }
                                game.nextTurn();
                                listener.printGame();
                            } catch (NoValidMoves ignored) {
                            }
                        }
                        case Protocol.GAMEOVER -> {
                            switch (protocolSplit[1]) {
                                case Protocol.DRAW -> listener.printGameOverDraw();
                                case Protocol.DISCONNECT -> listener.printGameOverDisconnected(protocolSplit[2]);
                                case Protocol.VICTORY -> listener.printGameOverVictory(protocolSplit[2]);
                            }
                        }
                        case Protocol.ERROR -> System.out.println(line);
                    }
                }
            }
        } catch (IOException e) {
            close();
        }
    }

    public void close() {
        try {
            socket.close();
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    public boolean send(String msg) {
        try {
            bw.write(msg);
            bw.newLine();
            bw.flush();
            return true;
        } catch (IOException e) {
            close();
            return false;
        }
    }

    public void sendMove(int moveIndex) {
        try {
            game.doMove(moveIndex);
            game.nextTurn();
            send(Protocol.sendMove(moveIndex));
        } catch (NoValidMoves ignored) {
            send(Protocol.sendMove(64));
        }

    }

    public boolean getLoggedIn() {
        return hasLoggedIn;
    }

    public void setPlayer(Player player) {
        this.player = player;
    }

    public String getUsername() {
        return username;
    }

    public void setUsername(String username) {
        this.username = username;
    }

    public OthelloGame getGame() {
        return game;
    }
}
