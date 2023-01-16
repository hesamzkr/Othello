package tictactoe.ai;

import tictactoe.model.Player;

import java.util.ArrayList;
import java.util.List;

public interface Node {

    Node getParent();

    State getState();

    List<Node> getChildArray();

    double getRewardForPlayer(Player player);
}
