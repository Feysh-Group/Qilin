/* Qilin - a Java Pointer Analysis Framework
 * Copyright (C) 2021-2030 Qilin developers
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as
 * published by the Free Software Foundation, either version 3.0 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Lesser Public License for more details.
 *
 * You should have received a copy of the GNU General Lesser Public
 * License along with this program.  If not, see
 * <https://www.gnu.org/licenses/lgpl-3.0.en.html>.
 */

package qilin.core.sets;

import qilin.core.PTA;
import qilin.core.pag.AllocNode;
import qilin.core.pag.Node;
import soot.util.ArrayNumberer;

/**
 * Abstract base class for points-to set visitors used to enumerate points-to sets.
 *
 * @author Ondrej Lhotak
 */
public abstract class P2SetVisitor {
    protected boolean returnValue = false;
    protected final ArrayNumberer<AllocNode> allocNodes;

    protected P2SetVisitor(PTA pta) {
        this.allocNodes = pta.getPag().getAllocNodeNumberer();
    }


    protected abstract void visit(Node n);

    public void visit(long idx) {
        Node node = allocNodes.get(idx);
        visit(node);
    }

    public boolean getReturnValue() {
        return returnValue;
    }
}
