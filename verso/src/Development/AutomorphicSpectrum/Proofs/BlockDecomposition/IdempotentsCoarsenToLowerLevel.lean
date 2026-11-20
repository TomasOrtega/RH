import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsLimHom
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.ContUniv

/- English proof (translation)
Establish `hmul : ∀ c d : J, (∑ c' with π c' = c, e c') * (∑ c' with π c' = d, e c') = if c = d then ∑ c' with π c' = c, e c' else 0`. Introduce `c d`. Rewrite using `[Finset.sum_mul_sum]`. Use `split_ifs with hcd`. Substitute `hcd` using the available equality.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i]`. Conclude with `he.idem i`. Introduce `j _ hji`. Conclude with `he.ortho hji.symm`.

Introduce `h`. Conclude with `absurd hi h`. Use `Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => he.ortho ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hcd ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)`.

Use `⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ * _ = _`. Rewrite using `[hmul, if_pos rfl]`. Express the relevant statement in the definitionally equal form `_ * _ = _`. Rewrite using `[hmul, if_neg hcd]`.

Rewrite using `[Finset.sum_fiberwise]`. Conclude with `he.complete`.
-/
theorem coi_fiber {R I J : Type} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (π : I → J) {e : I → R} (he : CompleteOrthogonalIdempotents e) :
    CompleteOrthogonalIdempotents (fun c : J => ∑ c' with π c' = c, e c') := by
  classical
  have hmul : ∀ c d : J, (∑ c' with π c' = c, e c') * (∑ c' with π c' = d, e c') =
      if c = d then ∑ c' with π c' = c, e c' else 0 := by
    intro c d
    rw [Finset.sum_mul_sum]
    split_ifs with hcd
    · subst hcd
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.sum_eq_single i]
      · exact he.idem i
      · intro j _ hji
        exact he.ortho hji.symm
      · intro h; exact absurd hi h
    · refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => he.ortho ?_
      rintro rfl
      exact hcd ((Finset.mem_filter.1 hi).2.symm.trans (Finset.mem_filter.1 hj).2)
  refine ⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩
  · change _ * _ = _
    rw [hmul, if_pos rfl]
  · change _ * _ = _
    rw [hmul, if_neg hcd]
  · rw [Finset.sum_fiberwise]
    exact he.complete

/- English proof (translation)
Proceed by induction on `d with`. Consider the case `zero => simp`. Consider the case `succ d ih`. Rewrite using `[pow_succ', pow_mul, ← add_assoc, h, ih]`.
-/
theorem chain_pow {M : Type} [Monoid M] {p : ℕ} {x : ℕ → M} (h : ∀ k, x (k + 1) ^ p = x k)
    (m d : ℕ) : x (m + d) ^ p ^ d = x m := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', pow_mul, ← add_assoc, h, ih]

/- English proof (translation)
Take `⟨d, hd⟩` from `sub_dvd_pow_sub_pow x y q`. Rewrite using `[hd, ← mul_assoc, h, zero_mul]`.
-/
theorem mul_sub_pow {S : Type} [CommRing S] {a x y : S} (h : a * (x - y) = 0) (q : ℕ) :
    a * (x ^ q - y ^ q) = 0 := by
  obtain ⟨d, hd⟩ := sub_dvd_pow_sub_pow x y q
  rw [hd, ← mul_assoc, h, zero_mul]

/- English proof (translation)
Establish `h0` using `map_natCast (ZMod.castHom h (ZMod M)) c.val`. Rewrite `h0` using `[ZMod.natCast_zmod_val]`. Rewrite using `[← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]`. Conclude with `h0.symm`.
-/
theorem val_modEq {N M : ℕ} [NeZero N] [NeZero M] (h : M ∣ N) (c : ZMod N) :
    c.val ≡ (ZMod.castHom h (ZMod M) c).val [MOD M] := by
  have h0 := map_natCast (ZMod.castHom h (ZMod M)) c.val
  rw [ZMod.natCast_zmod_val] at h0
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  exact h0.symm

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, chain_pow ε.succ]`.
-/
theorem sharp_xi_pow (ε : Eps l) (t : PAlg l) (m d : ℕ) :
    t.sharp (t.s (ε.e (m + d))) ^ l ^ d = t.sharp (t.s (ε.e m)) := by
  rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, chain_pow ε.succ]

/- English proof (translation)
Use `sharp_xi_pow ε t 0 m` as an intermediate fact. Rewrite `this` using `[zero_add]`. Rewrite using `[this]`. Conclude with `ε.sharp_e t`.
-/
theorem sharp_xi_period (ε : Eps l) (t : PAlg l) (m : ℕ) :
    t.sharp (t.s (ε.e m)) ^ l ^ m = 1 := by
  have := sharp_xi_pow ε t 0 m
  rw [zero_add] at this
  rw [this]
  exact ε.sharp_e t

/- English proof (translation)
Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le h`. Use `⟨coi_fiber _ he, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[(sharp_sum t _ e (fun i _ => he.idem i) (fun i _ j _ hij => he.ortho hij)).1, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun c' hc' => ?_` and prove the remaining obligations. Establish `hπ` using `(Finset.mem_filter.1 hc').2`.

Establish `h1` using `mul_sub_pow (hc c') (l ^ d)`. Rewrite `h1` using `[← map_pow, chain_pow hr, ← pow_mul, mul_comm c'.val, pow_mul, sharp_xi_pow]`. Establish `h2 : t.sharp (t.s (ε.e m)) ^ c'.val = t.sharp (t.s (ε.e m)) ^ c.val`. Establish `hv` using `val_modEq (pow_dvd_pow l h) c'`. Rewrite `hv` using `[hπ]`.

Rewrite using `[pow_eq_pow_mod c'.val (sharp_xi_period ε t m), pow_eq_pow_mod c.val (sharp_xi_period ε t m)]`. Conclude with `congrArg _ hv`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.
-/
theorem coi_descend (ε : Eps l) (t : PAlg l) (r : ℕ → t.A) (hr : ∀ m, r (m + 1) ^ l = r m)
    {m n : ℕ} (h : m ≤ n) (e : ZMod (l ^ n) → t.A) (he : CompleteOrthogonalIdempotents e)
    (hc : ∀ c, t.sharp (e c) * (t.sharp (r n) - t.sharp (t.s (ε.e n)) ^ c.val) = 0) :
    CompleteOrthogonalIdempotents
        (fun c : ZMod (l ^ m) => ∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') ∧
      ∀ c : ZMod (l ^ m), t.sharp (∑ c' with ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ m)) c' = c, e c') *
        (t.sharp (r m) - t.sharp (t.s (ε.e m)) ^ c.val) = 0 := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨coi_fiber _ he, fun c => ?_⟩
  rw [(sharp_sum t _ e (fun i _ => he.idem i) (fun i _ j _ hij => he.ortho hij)).1, Finset.sum_mul]
  refine Finset.sum_eq_zero fun c' hc' => ?_
  have hπ := (Finset.mem_filter.1 hc').2
  have h1 := mul_sub_pow (hc c') (l ^ d)
  rw [← map_pow, chain_pow hr, ← pow_mul, mul_comm c'.val, pow_mul, sharp_xi_pow] at h1
  have h2 : t.sharp (t.s (ε.e m)) ^ c'.val = t.sharp (t.s (ε.e m)) ^ c.val := by
    have hv := val_modEq (pow_dvd_pow l h) c'
    rw [hπ] at hv
    rw [pow_eq_pow_mod c'.val (sharp_xi_period ε t m), pow_eq_pow_mod c.val (sharp_xi_period ε t m)]
    exact congrArg _ hv
  rwa [h2] at h1

end GlobalTheory.CompanionTheory.ContUniv
