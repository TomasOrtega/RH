import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j hij`. Conclude with `(Submodule.mem_bot A).1 ((h i j).2 hij)`. Introduce `h i j`. Conclude with `⟨fun _ => Submodule.mem_top, fun hij => by rw [h i j hij]; exact Submodule.zero_mem _⟩`.
-/
private theorem mem_ev_iff_apply_eq_zero_off_diagonal_blocks {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (n a : ℕ)
    (Z : Matrix (Fin n) (Fin n) R) :
    Z ∈ Ev A R n a ↔ ∀ i j : Fin n, ¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
  constructor
  · intro h i j hij
    exact (Submodule.mem_bot A).1 ((h i j).2 hij)
  · intro h i j
    exact ⟨fun _ => Submodule.mem_top, fun hij => by rw [h i j hij]; exact Submodule.zero_mem _⟩

/- English proof (translation)
Introduce `l _ F n x hl hg`. Take `⟨g₀, hg₀⟩` from `hg`. Establish `hev : ∀ g : F.G₀, (mat x.ρ g).map (algebraMap x.A (FractionRing x.A)) ∈ Ev (FractionRing x.A) (FractionRing x.A) n x.a`. Introduce `g`. Rewrite using `[mem_ev_iff_apply_eq_zero_off_diagonal_blocks]`.

Introduce `i j hij`. Establish `h0` using `(mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 (x.blk g) i j hij`. Rewrite using `[Matrix.map_apply, h0, map_zero]`. Establish `hmap : ∀ M ∈ Submodule.span x.A ((mat x.ρ) '' (F.G' : Set F.G₀)), M.map (algebraMap x.A (FractionRing x.A)) ∈ Submodule.span (FractionRing x.A) ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀))`. Introduce `M hM`.

Proceed by induction on `hM using Submodule.span_induction with`. Consider the case `mem M hM`. Take `⟨g, hg, rfl⟩` from `hM`. Conclude with `Submodule.subset_span ⟨g, hg, rfl⟩`. Consider the case `zero`.

Establish `h0 : (0 : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A (FractionRing x.A)) = 0`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`.

Consider the case `add M N _ _ hM hN`. Establish `h0 : (M + N).map (algebraMap x.A (FractionRing x.A)) = M.map (algebraMap x.A (FractionRing x.A)) + N.map (algebraMap x.A (FractionRing x.A))`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[h0]`.

Conclude with `Submodule.add_mem _ hM hN`. Consider the case `smul c M _ hM`. Establish `h0 : (c • M).map (algebraMap x.A (FractionRing x.A)) = algebraMap x.A (FractionRing x.A) c • M.map (algebraMap x.A (FractionRing x.A))`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite using `[h0]`. Conclude with `Submodule.smul_mem _ _ hM`. Establish `hsingle : ∀ i j : Fin n, ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → Matrix.single i j (1 : FractionRing x.A) ∈ Submodule.span (FractionRing x.A) ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀))`. Introduce `i j hij`. Establish `hZ : Matrix.single i j (1 : x.A) ∈ Ev x.A x.A n x.a`.

Rewrite using `[mem_ev_iff_apply_eq_zero_off_diagonal_blocks]`. Introduce `k m hkm`. Rewrite using `[Matrix.single_apply, if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hkm hij`.

Take `⟨s, hs⟩` from `x.span _ hZ`. Establish `key` using `hmap _ hs`. Establish `h1 : ((PowerSeries.X : x.A) ^ s • Matrix.single i j (1 : x.A)).map (algebraMap x.A (FractionRing x.A)) = algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) • Matrix.single i j (1 : FractionRing x.A)`. Use extensionality with `k m`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `key` using `[h1]`. Establish `hne : algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) ≠ 0`. Introduce `h`. Apply `pow_ne_zero s (PowerSeries.X_ne_zero (R := x.K))` to reduce the goal to its premises.

Apply `IsFractionRing.injective x.A (FractionRing x.A)` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Establish `h2` using `Submodule.smul_mem _ (algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s))⁻¹ key`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hne, one_smul]`. Then use the resulting hypothesis. Establish `hspan : Submodule.span (FractionRing x.A) ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) = Ev (FractionRing x.A) (FractionRing x.A) n x.a`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, -, rfl⟩`. Conclude with `hev g`. Introduce `Z hZ`.

Rewrite using `[Matrix.matrix_eq_sum_single Z]`. Use `Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))` and prove the remaining obligations. Distinguish the cases in `hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)`. Establish `h3 : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : FractionRing x.A)`. Rewrite using `[Matrix.smul_single, smul_eq_mul, mul_one]`.

Rewrite using `[h3]`. Conclude with `Submodule.smul_mem _ _ (hsingle i j hij)`. Rewrite using `[(mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 hZ i j hij, Matrix.single_zero]`. Conclude with `Submodule.zero_mem _`. Establish `h2 : IsUnit (2 : ℤ_[l])`.

Assume the negation of the conclusion as `h`. Establish `hm : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l]` using `(IsLocalRing.mem_maximalIdeal _).2 h`. Rewrite `hm` using `[← PadicInt.ker_toZMod, RingHom.mem_ker]`. Establish `h4 : ((2 : ℕ) : ZMod l) = 0`. Rewrite using `[Nat.cast_ofNat, ← hm, map_ofNat]`.

Establish `h5 : l ∣ 2` using `(ZMod.natCast_eq_zero_iff 2 l).1 h4`. Conclude with `hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h5)`. Establish `hc : ∀ g : F.G₀, F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ)`. Introduce `g`. Use `show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε (g : F.Γ)`.

Rewrite using `[map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_inv_cancel_right]`. Use `⟨DetFr.mk ?_ x.a x.a_pos x.a_le F.G' ?_ (F.eps x.A (FractionRing x.A)) ?_ g₀ ?_ ((algebraMap x.A (FractionRing x.A)).mapMatrix.toMonoidHom.comp (mat x.ρ)) hspan hev F.conj ?_ ?_ (fun g => Units.map (algebraMap x.A (FractionRing x.A)).toMonoidHom ((F.eps ℤ_[l] x.A g) ^ (1 - (n : ℤ …` and prove the remaining obligations. Establish `h6` using `(h2.map ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A))).ne_zero`. Rewrite `h6` using `[RingHom.comp_apply, map_ofNat, map_ofNat]`. Conclude with `h6`.

Introduce `g h`. Rewrite using `[GFrame.G', MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one, mul_inv_eq_iff_eq_mul, mul_comm]`. Introduce `g hg`. Rewrite `hg` using `[GFrame.G', MonoidHom.mem_ker]`. Use `show Units.map _ ((F.ε.comp F.η.ker.subtype) g) = 1`.

Rewrite using `[hg, map_one]`. Introduce `h`. Apply `hg₀` to reduce the goal to its premises. Establish `h7` using `congrArg Units.val h`. Express the relevant statement in the definitionally equal form `algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l])) = 1 at h7`.

Establish `h8 : ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ RingHom.ker ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A))`. Rewrite using `[RingHom.mem_ker, map_sub, RingHom.comp_apply, h7, map_one, sub_self]`. Establish `h9` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) h8`. Rewrite `h9` using `[← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero]`. Conclude with `h9`.

Introduce `g`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (g : F.Γ)`. Combine the equalities or inequalities in the displayed calculation. Introduce `g show Units.map _ ((F.ε.comp F.η.ker.subtype) (F.conj g)) = Units.map _ ((F.ε.comp F.η.ker.subtype) g)`.

Rewrite using `[MonoidHom.comp_apply, MonoidHom.comp_apply]`. Conclude with `congrArg _ (hc g)`. Introduce `g show ((mat x.ρ g).map (algebraMap x.A (FractionRing x.A)))ᵀ * (mat x.ρ (F.conj g)).map (algebraMap x.A (FractionRing x.A)) = (algebraMap x.A (FractionRing x.A) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) • 1`. Establish `h0` using `x.form g`. Rewrite `h0` using `[Units.val_one, Matrix.mul_one]`.

Rewrite using `[← Matrix.transpose_map, ← Matrix.map_mul, h0]`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem UpperTheory.V.Pa.Det.detFr :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n), l ≠ 2 → (∃ g : F.G₀, PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) ≠ 1) → ∃ D : DetFr (FractionRing x.A) F.G₀ n, D.a = x.a ∧ D.G' = F.G' ∧ (∀ g, D.r g = x.ρX (FractionRing x.A) g) ∧ D.σ = F.conj ∧ ∀ g : F.G₀, D.χF g = algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A (F.ε g : ℤ_[l])) := by
  intro l _ F n x hl hg
  obtain ⟨g₀, hg₀⟩ := hg
  have hev : ∀ g : F.G₀, (mat x.ρ g).map (algebraMap x.A (FractionRing x.A)) ∈
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    intro g
    rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
    intro i j hij
    have h0 := (mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 (x.blk g) i j hij
    rw [Matrix.map_apply, h0, map_zero]
  have hmap : ∀ M ∈ Submodule.span x.A ((mat x.ρ) '' (F.G' : Set F.G₀)),
      M.map (algebraMap x.A (FractionRing x.A)) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      exact Submodule.subset_span ⟨g, hg, rfl⟩
    | zero =>
      have h0 : (0 : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A (FractionRing x.A)) = 0 := by
        ext i j
        simp
      rw [h0]
      exact Submodule.zero_mem _
    | add M N _ _ hM hN =>
      have h0 : (M + N).map (algebraMap x.A (FractionRing x.A)) =
          M.map (algebraMap x.A (FractionRing x.A)) + N.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.add_mem _ hM hN
    | smul c M _ hM =>
      have h0 : (c • M).map (algebraMap x.A (FractionRing x.A)) =
          algebraMap x.A (FractionRing x.A) c • M.map (algebraMap x.A (FractionRing x.A)) := by
        ext i j
        simp
      rw [h0]
      exact Submodule.smul_mem _ _ hM
  have hsingle : ∀ i j : Fin n, ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) →
      Matrix.single i j (1 : FractionRing x.A) ∈ Submodule.span (FractionRing x.A)
        ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) := by
    intro i j hij
    have hZ : Matrix.single i j (1 : x.A) ∈ Ev x.A x.A n x.a := by
      rw [mem_ev_iff_apply_eq_zero_off_diagonal_blocks]
      intro k m hkm
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact hkm hij
    obtain ⟨s, hs⟩ := x.span _ hZ
    have key := hmap _ hs
    have h1 : ((PowerSeries.X : x.A) ^ s • Matrix.single i j (1 : x.A)).map
        (algebraMap x.A (FractionRing x.A)) =
        algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) • Matrix.single i j (1 : FractionRing x.A) := by
      ext k m
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs <;> simp
    rw [h1] at key
    have hne : algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s) ≠ 0 := by
      intro h
      apply pow_ne_zero s (PowerSeries.X_ne_zero (R := x.K))
      apply IsFractionRing.injective x.A (FractionRing x.A)
      rw [h, map_zero]
    have h2 := Submodule.smul_mem _ (algebraMap x.A (FractionRing x.A) ((PowerSeries.X : x.A) ^ s))⁻¹ key
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  have hspan : Submodule.span (FractionRing x.A)
      ((fun g : F.G₀ => (mat x.ρ g).map (algebraMap x.A (FractionRing x.A))) '' (F.G' : Set F.G₀)) =
      Ev (FractionRing x.A) (FractionRing x.A) n x.a := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨g, -, rfl⟩
      exact hev g
    · intro Z hZ
      rw [Matrix.matrix_eq_sum_single Z]
      refine Submodule.sum_mem _ (fun i _ => Submodule.sum_mem _ (fun j _ => ?_))
      by_cases hij : ((i : ℕ) < x.a ↔ (j : ℕ) < x.a)
      · have h3 : Matrix.single i j (Z i j) = Z i j • Matrix.single i j (1 : FractionRing x.A) := by
          rw [Matrix.smul_single, smul_eq_mul, mul_one]
        rw [h3]
        exact Submodule.smul_mem _ _ (hsingle i j hij)
      · rw [(mem_ev_iff_apply_eq_zero_off_diagonal_blocks _ _ _).1 hZ i j hij, Matrix.single_zero]
        exact Submodule.zero_mem _
  have h2 : IsUnit (2 : ℤ_[l]) := by
    by_contra h
    have hm : (2 : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := (IsLocalRing.mem_maximalIdeal _).2 h
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
    have h4 : ((2 : ℕ) : ZMod l) = 0 := by
      rw [Nat.cast_ofNat, ← hm, map_ofNat]
    have h5 : l ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).1 h4
    exact hl ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 h5)
  have hc : ∀ g : F.G₀, F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
    intro g
    show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = F.ε (g : F.Γ)
    rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_inv_cancel_right]
  refine ⟨DetFr.mk ?_ x.a x.a_pos x.a_le F.G' ?_ (F.eps x.A (FractionRing x.A)) ?_ g₀ ?_
    ((algebraMap x.A (FractionRing x.A)).mapMatrix.toMonoidHom.comp (mat x.ρ)) hspan hev F.conj ?_ ?_
    (fun g => Units.map (algebraMap x.A (FractionRing x.A)).toMonoidHom
      ((F.eps ℤ_[l] x.A g) ^ (1 - (n : ℤ)))) ?_, rfl, rfl, fun g => rfl, rfl, fun g => rfl⟩
  · have h6 := (h2.map ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A))).ne_zero
    rw [RingHom.comp_apply, map_ofNat, map_ofNat] at h6
    exact h6
  · intro g h
    rw [GFrame.G', MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
      mul_inv_eq_iff_eq_mul, mul_comm]
  · intro g hg
    rw [GFrame.G', MonoidHom.mem_ker] at hg
    show Units.map _ ((F.ε.comp F.η.ker.subtype) g) = 1
    rw [hg, map_one]
  · intro h
    apply hg₀
    have h7 := congrArg Units.val h
    change algebraMap x.A (FractionRing x.A) (algebraMap ℤ_[l] x.A ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l])) = 1 at h7
    have h8 : ((F.ε g₀ : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈
        RingHom.ker ((algebraMap x.A (FractionRing x.A)).comp (algebraMap ℤ_[l] x.A)) := by
      rw [RingHom.mem_ker, map_sub, RingHom.comp_apply, h7, map_one, sub_self]
    have h9 := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top _) h8
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at h9
    exact h9
  · intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (g : F.Γ)
    calc F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = (F.c * F.c) * (g : F.Γ) * (F.c * F.c)⁻¹ := by group
      _ = (g : F.Γ) := by rw [F.c_sq]; group
  · intro g
    show Units.map _ ((F.ε.comp F.η.ker.subtype) (F.conj g)) = Units.map _ ((F.ε.comp F.η.ker.subtype) g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact congrArg _ (hc g)
  · intro g
    show ((mat x.ρ g).map (algebraMap x.A (FractionRing x.A)))ᵀ *
        (mat x.ρ (F.conj g)).map (algebraMap x.A (FractionRing x.A)) =
        (algebraMap x.A (FractionRing x.A) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) • 1
    have h0 := x.form g
    rw [Units.val_one, Matrix.mul_one] at h0
    rw [← Matrix.transpose_map, ← Matrix.map_mul, h0]
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
