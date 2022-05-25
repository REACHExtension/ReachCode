package edu.mit.csail.sdg.alloy4whole;

import javax.swing.BoxLayout;
import javax.swing.Icon;
import javax.swing.ImageIcon;
import javax.swing.JLabel;

import edu.mit.csail.sdg.alloy4.OurUtil;

public class AUnitGuiUtil {

    public AUnitGuiUtil() {
    }

    public static JLabel makeLabel(String title, String imageLocation) {
        return new JLabel(title, new ImageIcon(imageLocation), JLabel.LEFT);
    }

    public static TabPanel makeTab(JLabel label, JLabel labelClose, Icon active, Icon inactive) {
        JLabel space = new JLabel(" ");
        JLabel black = new JLabel("", OurUtil.loadIcon("images/black.png"), JLabel.LEFT);
        label.setHorizontalAlignment(JLabel.LEFT);
        TabPanel tab = new TabPanel(label, labelClose, active, inactive);
        tab.add(space);
        tab.add(label);
        tab.add(labelClose);
        tab.add(space);
        tab.add(black);
        BoxLayout boxLayoutAUnit = new BoxLayout(tab, BoxLayout.X_AXIS);
        tab.setLayout(boxLayoutAUnit);
        tab.setAlignmentX(1.0f);
        tab.setAlignmentY(1.0f);
        return tab;
    }

    public static TabPanel makeTab(JLabel label, Icon active, Icon inactive) {
        JLabel space = new JLabel(" ");
        JLabel black = new JLabel("", OurUtil.loadIcon("images/black.png"), JLabel.LEFT);
        label.setHorizontalAlignment(JLabel.LEFT);
        TabPanel tab = new TabPanel(label, new JLabel(), active, inactive);
        tab.add(space);
        tab.add(label);
        tab.add(space);
        tab.add(black);
        BoxLayout boxLayoutAUnit = new BoxLayout(tab, BoxLayout.X_AXIS);
        tab.setLayout(boxLayoutAUnit);
        tab.setAlignmentX(1.0f);
        tab.setAlignmentY(1.0f);
        return tab;
    }
}
