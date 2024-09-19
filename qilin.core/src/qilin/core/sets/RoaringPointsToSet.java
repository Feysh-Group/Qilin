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

import org.roaringbitmap.RoaringBitmap;
import soot.util.BitSetIterator;
import soot.util.BitVector;

import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;

/**
 * Hybrid implementation of points-to set, which uses an explicit array for small sets, and a bit vector for large sets.
 *
 * @author Ondrej Lhotak
 */
public final class RoaringPointsToSet extends PointsToSetInternal {

    private RoaringBitmap bits;

    /**
     * Returns true if this set contains no run-time objects.
     */
    @Override
    public boolean isEmpty() {
        return bits == null || bits.isEmpty();
    }

    @Override
    public void clear() {
        bits = null;
    }

    private void nativeAddAll(PointsToSetInternal other, PointsToSetInternal exclude) {
        if (other instanceof RoaringPointsToSet && (exclude == null || exclude instanceof RoaringPointsToSet)) {
            RoaringBitmap otherBits = ((RoaringPointsToSet) other).bits;
            if (otherBits == null) {
                return;
            }
            RoaringBitmap or;
            if (exclude != null) {
                RoaringBitmap excludeBits = ((RoaringPointsToSet) exclude).bits;
                if (excludeBits != null) {
                    or = RoaringBitmap.andNot(otherBits, excludeBits);
                } else {
                    or = otherBits;
                }
            } else {
                or = otherBits;
            }
            RoaringBitmap bits = this.bits;
            if (bits == null) {
                bits = new RoaringBitmap();
                this.bits = bits;
            }
            bits.or(or);
            return;
        }
        for (Iterator<Integer> it = other.iterator(); it.hasNext(); ) {
            int idx = it.next();
            if (exclude == null || !exclude.contains(idx)) {
                add(idx);
            }
        }
    }

    /**
     * Adds contents of other into this set, returns true if this set changed.
     */
    public void addAll(final PointsToSetInternal other, final PointsToSetInternal exclude) {
        if (other == null) {
            return;
        }
        if (other instanceof DoublePointsToSet dpts) {
            nativeAddAll(dpts.getNewSet(), exclude);
            nativeAddAll(dpts.getOldSet(), exclude);
            return;
        }
        nativeAddAll(other, exclude);
    }

    @Override
    public Iterator<Integer> iterator() {
        if (bits == null) {
            return Collections.emptyIterator();
        }
        return bits.iterator();
    }


    /** Returns number of bits in the underlying array. */
    @Override
    public int size() {
        if (this.bits == null || this.bits.isEmpty()) {
            return 0;
        }
        int lastBit = Math.max(this.bits.last() + 1, 64);
        int remainder = lastBit % 64;
        return remainder == 0 ? lastBit : lastBit + 64 - remainder;
    }

    @Override
    public PointsToSetInternal lessMem() {
        return this;
    }

    /**
     * Calls v's visit method on all nodes in this set.
     */
    public boolean forall(P2SetVisitor v) {
        if (bits != null) {
            for (Integer bit : bits) {
                v.visit(bit);
            }
        }
        return v.getReturnValue();
    }

    /**
     * Returns true iff the set contains node idx.
     */
    public boolean contains(int idx) {
        if (bits != null) {
            return bits.contains(idx);
        } else {
            return false;
        }
    }

    /**
     * Adds idx to this set, returns true if idx was not already in this set.
     */
    public boolean add(int idx) {
        if (bits == null) {
            bits = new RoaringBitmap();
        }
        return bits.checkedAdd(idx);
    }
}
