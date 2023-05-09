/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

use highway::{HighwayHasher, Key};
use libfuzzer_sys::arbitrary::{self, Arbitrary};
use serde::{Deserialize, Serialize};
use std::hash::{BuildHasher, Hash};
use std::ops::{Deref, DerefMut};

#[derive(Default)]
pub struct FixedHash();

impl BuildHasher for FixedHash {
    type Hasher = HighwayHasher;

    fn build_hasher(&self) -> Self::Hasher {
        let key = Key([1, 3, 3, 7]);
        HighwayHasher::new(key)
    }
}

impl<K, V> From<std::collections::HashMap<K, V>> for HashMap<K, V>
where
    K: Eq + Hash,
{
    fn from(map: std::collections::HashMap<K, V>) -> Self {
        HashMap(map.into_iter().collect())
    }
}

impl<K, V> From<HashMap<K, V>> for std::collections::HashMap<K, V>
where
    K: Eq + Hash,
{
    fn from(val: HashMap<K, V>) -> Self {
        val.0.into_iter().collect()
    }
}

#[repr(transparent)]
#[derive(Debug, Serialize, Arbitrary, Deserialize)]
#[serde(transparent)]
pub struct HashMap<K: Eq + Hash, V>(std::collections::HashMap<K, V, FixedHash>);

impl<K, V> Default for HashMap<K, V>
where
    K: Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> HashMap<K, V>
where
    K: Eq + Hash,
{
    pub fn new() -> Self {
        HashMap(std::collections::HashMap::with_hasher(FixedHash()))
    }

    pub fn into_values(self) -> impl Iterator<Item = V> {
        self.0.into_values()
    }
}

impl<K, V> FromIterator<(K, V)> for HashMap<K, V>
where
    K: Eq + Hash,
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = (K, V)>,
    {
        HashMap(std::collections::HashMap::from_iter(iter))
    }
}

impl<'a, K, V> IntoIterator for &'a HashMap<K, V>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a V);
    type IntoIter = std::collections::hash_map::Iter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter()
    }
}

impl<'a, K, V> IntoIterator for &'a mut HashMap<K, V>
where
    K: Eq + Hash,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = std::collections::hash_map::IterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.iter_mut()
    }
}

impl<K, V> IntoIterator for HashMap<K, V>
where
    K: Eq + Hash,
{
    type Item = (K, V);
    type IntoIter = std::collections::hash_map::IntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<K, V> Clone for HashMap<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn clone(&self) -> Self {
        Self(self.iter().map(|(k, v)| (k.clone(), v.clone())).collect())
    }
}

impl<K, V> Deref for HashMap<K, V>
where
    K: Eq + Hash,
{
    type Target = std::collections::HashMap<K, V, FixedHash>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, V> DerefMut for HashMap<K, V>
where
    K: Eq + Hash,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<K, V> AsRef<std::collections::HashMap<K, V, FixedHash>> for HashMap<K, V>
where
    K: Eq + Hash,
{
    fn as_ref(&self) -> &std::collections::HashMap<K, V, FixedHash> {
        &self.0
    }
}

#[repr(transparent)]
#[derive(Debug, PartialEq, Eq, Arbitrary, Serialize, Deserialize)]
#[serde(transparent)]
pub struct HashSet<V: Eq + Hash>(std::collections::HashSet<V, FixedHash>);

impl<V: Eq + Hash> HashSet<V> {
    pub fn new() -> Self {
        Self(std::collections::HashSet::with_hasher(FixedHash()))
    }
}

impl<V: Eq + Hash> Deref for HashSet<V> {
    type Target = std::collections::HashSet<V, FixedHash>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<V> DerefMut for HashSet<V>
where
    V: Eq + Hash,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<V: Eq + Hash> AsRef<std::collections::HashSet<V, FixedHash>> for HashSet<V> {
    fn as_ref(&self) -> &std::collections::HashSet<V, FixedHash> {
        &self.0
    }
}

impl<V> FromIterator<V> for HashSet<V>
where
    V: Eq + Hash,
{
    fn from_iter<I: IntoIterator<Item = V>>(iter: I) -> Self {
        HashSet(iter.into_iter().collect())
    }
}

impl<V> From<std::collections::HashSet<V>> for HashSet<V>
where
    V: Eq + Hash,
{
    fn from(m: std::collections::HashSet<V>) -> Self {
        Self(m.into_iter().collect())
    }
}

impl<V> From<HashSet<V>> for std::collections::HashSet<V>
where
    V: Eq + Hash,
{
    fn from(val: HashSet<V>) -> Self {
        val.0.into_iter().collect()
    }
}

impl<V> IntoIterator for HashSet<V>
where
    V: Eq + Hash,
{
    type Item = V;
    type IntoIter = std::collections::hash_set::IntoIter<V>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

impl<V> Default for HashSet<V>
where
    V: Eq + Hash,
{
    fn default() -> Self {
        Self::new()
    }
}
