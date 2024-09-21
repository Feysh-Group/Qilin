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

package qilin.util;

import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.ConcurrentHashMap;

import org.roaringbitmap.RoaringBitmap;
import soot.SootField;
import soot.jimple.spark.pag.SparkField;
import soot.util.*;

public class DataFactory {
    public static <T> List<T> createList() {
        return new ArrayList<>();
//        return new CopyOnWriteArrayList<>();
    }

    public static <T> Set<T> createSet() {
        return new HashSet<>();
//        return ConcurrentHashMap.newKeySet();
    }

    public static <T> Set<T> createConcurrentSet(int initCapacity) {
        return Collections.newSetFromMap(new ConcurrentHashMap<>(initCapacity));
    }

    public static <T> Set<T> createConcurrentSet() {
        return Collections.newSetFromMap(new ConcurrentHashMap<>());
    }

    public static <T> Set<T> createSet(int initCapacity) {
        return new HashSet<>(initCapacity);
//        return ConcurrentHashMap.newKeySet(initCapacity);
    }

    public static <K, V> Map<K, V> createMap() {
        return new HashMap<>();
//        return new ConcurrentHashMap<>();
    }

    public static <K, V> Map<K, V> createMap(int initCapacity) {
        return new HashMap<>(initCapacity);
//        return new ConcurrentHashMap<>(initCapacity);
    }

    public static <K, V> ConcurrentHashMap<K, V> createConcurrentMap(int initCapacity) {
        return new ConcurrentHashMap<>(initCapacity);
    }


    public static <K, V> ConcurrentHashMap<K, V> createConcurrentMap() {
        return new ConcurrentHashMap<>();
    }

    public static <N extends Numberable> INumbererSet<N> createAddThreadSafeBitSet(Numberer<? super N> numberer) {
        //noinspection unchecked
        return new NumbererSet<>((Numberer<N>)numberer);
    }

    public static <N extends Numberable> INumbererSet<N> createLessMemBitSet(Numberer<? super N> numberer) {
        //noinspection unchecked
        return new RoaringNumbererSet<>(new RoaringBitmap(), (Numberer<N>)numberer);
    }

    public static <K, V> Map<K, V> small(Map<K, V> m) {
        int sz = m.size();
        if (sz == 1) {
            Map.Entry<K, V> e = m.entrySet().iterator().next();
            return Collections.singletonMap(e.getKey(), e.getValue());
        } else if (sz == 0) {
            return Collections.emptyMap();
        } else {
            return m;
        }
    }

    public static <E> Set<E> small(Set<E> s) {
        int sz = s.size();
        if (sz == 1) {
            E e = s.iterator().next();
            return Collections.singleton(e);
        } else if (sz == 0) {
            return Collections.emptySet();
        } else if (sz <= 16){
            return new ArraySet<>(s);
        } else {
            return s;
        }
    }

    public static <K extends Numberable, N extends Numberable, M extends Map<K, Set<N>>> M small(M map, Numberer<? super N> valueNumberer) {
        map.replaceAll((k, v) -> DataFactory.createLessMemBitSet(valueNumberer));
        return map;
    }
}
