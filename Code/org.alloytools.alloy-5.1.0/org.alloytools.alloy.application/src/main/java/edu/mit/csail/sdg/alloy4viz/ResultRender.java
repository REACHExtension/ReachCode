package edu.mit.csail.sdg.alloy4viz;

import java.awt.Component;

import javax.swing.JLabel;
import javax.swing.JTree;
import javax.swing.tree.DefaultMutableTreeNode;
import javax.swing.tree.TreeCellRenderer;

public class ResultRender implements TreeCellRenderer {

    private JLabel label;

    ResultRender() {
        label = new JLabel();
    }

    public Component getTreeCellRendererComponent(JTree tree, Object value, boolean selected, boolean expanded, boolean leaf, int row, boolean hasFocus) {
        Object o = ((DefaultMutableTreeNode) value).getUserObject();
        if (o instanceof ResultTreeNode) {
            ResultTreeNode node = (ResultTreeNode) o;
            label.setText(node.info);
        }
        return label;
    }
}

