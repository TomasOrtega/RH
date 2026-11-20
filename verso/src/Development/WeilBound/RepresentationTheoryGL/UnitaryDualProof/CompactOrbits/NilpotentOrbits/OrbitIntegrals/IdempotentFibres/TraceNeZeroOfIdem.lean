import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.T.Nil.Orb.Ofib

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Establish `he' : IsIdempotentElem (Matrix.toLin' e)`. Establish `h2 : Matrix.toLin' (e * e) = Matrix.toLin' e` using `by rw [he.eq]`. Rewrite `h2` using `[Matrix.toLin'_mul]`. Conclude with `h2`. Introduce `h`.

Apply `h0` to reduce the goal to its premises. Establish `ht : LinearMap.trace k (Fin n → k) (Matrix.toLin' e) = 0`. Rewrite using `[LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']`. Conclude with `h`. Establish `h1` using `(LinearMap.IsIdempotentElem.trace_eq_zero_iff (e := Matrix.toLin' e) he').1 ht`.

Conclude with `Matrix.toLin'.injective (by rw [h1, map_zero])`.
-/
theorem trace_ne_zero_of_idem [CharZero k] {e : Matrix (Fin n) (Fin n) k} (he : IsIdempotentElem e) (h0 : e ≠ 0) :
    trace e ≠ 0 := by
  have he' : IsIdempotentElem (Matrix.toLin' e) := by
    have h2 : Matrix.toLin' (e * e) = Matrix.toLin' e := by rw [he.eq]
    rw [Matrix.toLin'_mul] at h2
    exact h2
  intro h
  apply h0
  have ht : LinearMap.trace k (Fin n → k) (Matrix.toLin' e) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    exact h
  have h1 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff (e := Matrix.toLin' e) he').1 ht
  exact Matrix.toLin'.injective (by rw [h1, map_zero])

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Set `W : ℕ → Submodule k (Matrix (Fin n) (Fin n) k)` to `fun j => (Subalgebra.toSubmodule Z).map (LinearMap.mulLeft k (c ^ j))`. Establish `hmono : ∀ j, W (j + 1) ≤ W j`. Introduce `j x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.1 hx`. Use `Submodule.mem_map.2 ⟨c * y, Z.mul_mem hc hy, ?_⟩` and prove the remaining obligations.

Simplify using `[pow_succ, mul_assoc]`. Establish `hex : ∃ j, W (j + 1) = W j`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hlt : ∀ j, Module.finrank k (W (j + 1)) < Module.finrank k (W j)` using `fun j => Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono j) (hne j))`.

Establish `hb : ∀ j, Module.finrank k (W j) + j ≤ Module.finrank k (W 0)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => have := hlt j`.

Use linear arithmetic over natural numbers and integers. Establish `h1` using `hb (Module.finrank k (Matrix (Fin n) (Fin n) k) + 1)`. Establish `h2` using `Submodule.finrank_le (W 0)`. Use linear arithmetic over natural numbers and integers. Take `⟨m, hm⟩` from `hex`.

Establish `hcm : c ^ m ∈ W m` using `Submodule.mem_map.2 ⟨1, Z.one_mem, by simp⟩`. Rewrite `hcm` using `[← hm]`. Take `⟨d, hd, e⟩` from `Submodule.mem_map.1 hcm`. Conclude with `⟨m, d, hd, by simpa using e.symm⟩`.
-/
theorem exists_pow_eq {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) :
    ∃ (m : ℕ) (d : Matrix (Fin n) (Fin n) k), d ∈ Z ∧ c ^ m = c ^ (m + 1) * d := by
  let W : ℕ → Submodule k (Matrix (Fin n) (Fin n) k) := fun j =>
    (Subalgebra.toSubmodule Z).map (LinearMap.mulLeft k (c ^ j))
  have hmono : ∀ j, W (j + 1) ≤ W j := by
    intro j x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    refine Submodule.mem_map.2 ⟨c * y, Z.mul_mem hc hy, ?_⟩
    simp [pow_succ, mul_assoc]
  have hex : ∃ j, W (j + 1) = W j := by
    by_contra hne
    push Not at hne
    have hlt : ∀ j, Module.finrank k (W (j + 1)) < Module.finrank k (W j) := fun j =>
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (hmono j) (hne j))
    have hb : ∀ j, Module.finrank k (W j) + j ≤ Module.finrank k (W 0) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => have := hlt j; omega
    have h1 := hb (Module.finrank k (Matrix (Fin n) (Fin n) k) + 1)
    have h2 := Submodule.finrank_le (W 0)
    omega
  obtain ⟨m, hm⟩ := hex
  have hcm : c ^ m ∈ W m := Submodule.mem_map.2 ⟨1, Z.one_mem, by simp⟩
  rw [← hm] at hcm
  obtain ⟨d, hd, e⟩ := Submodule.mem_map.1 hcm
  exact ⟨m, d, hd, by simpa using e.symm⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Take `⟨m, d, hd, hmd⟩` from `exists_pow_eq hc`. Establish `hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a` using `hZ.1`. Establish `hdc : d * c = c * d` using `hcomm d hd c hc`. Establish `key : ∀ j, c ^ m = c ^ (m + j) * d ^ j`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`. Rewrite using `[ih]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← pow_add, pow_succ' d j, show j + (m + 1) = m + (j + 1) by omega]`. Use `set e := c ^ m * d ^ m with he_def`. Establish `hcd : Commute c d` using `by rw [Commute, SemiconjBy, hdc]`. Establish `he_idem : IsIdempotentElem e`. Unfold `IsIdempotentElem`.

Establish `h2` using `key m`. Combine the equalities or inequalities in the displayed calculation. Establish `he_mem : e ∈ Z` using `Z.mul_mem (Z.pow_mem hc m) (Z.pow_mem hd m)`. Assume the negation of the conclusion as `hne`. Distinguish the cases in `he0 : e = 0`.

Establish `hcm0 : c ^ m = 0`. Establish `h2` using `key m`. Rewrite using `[h2, pow_add, mul_assoc, ← he_def, he0, mul_zero]`. Establish `hnil : IsNilpotent (⟨c, hc⟩ : Z)` using `⟨m, Subtype.ext (by simpa using hcm0)⟩`. Use `hZ.2` as an intermediate fact.

Use `hnil.eq_zero` as an intermediate fact. Conclude with `hne (by simpa using congrArg Subtype.val this)`. Establish `hb : c ^ m * d ^ (m + 1) ∈ Z` using `Z.mul_mem (Z.pow_mem hc m) (Z.pow_mem hd _)`. Establish `hbe : c ^ m * d ^ (m + 1) * c = e`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, ← (hcd.pow_right (m + 1)).eq]`. Use `_ = c ^ (m + 1) * (d * d ^ m) := by rw [← mul_assoc, ← pow_succ, pow_succ' d m]`. Use `_ = e := by rw [← mul_assoc, ← hmd]`. Conclude with `trace_ne_zero_of_idem he_idem he0 (by rw [← hbe]; exact h _ hb)`.
-/
theorem eq_zero_of_trace [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (h : ∀ b ∈ Z, trace (b * c) = 0) : c = 0 := by
  obtain ⟨m, d, hd, hmd⟩ := exists_pow_eq hc
  have hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := hZ.1
  have hdc : d * c = c * d := hcomm d hd c hc

  have key : ∀ j, c ^ m = c ^ (m + j) * d ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [ih]
      calc c ^ (m + j) * d ^ j = c ^ j * c ^ m * d ^ j := by rw [← pow_add, add_comm]
        _ = c ^ j * (c ^ (m + 1) * d) * d ^ j := by rw [← hmd]
        _ = c ^ j * c ^ (m + 1) * (d * d ^ j) := by simp only [mul_assoc]
        _ = c ^ (m + (j + 1)) * d ^ (j + 1) := by
          rw [← pow_add, pow_succ' d j, show j + (m + 1) = m + (j + 1) by omega]
  set e := c ^ m * d ^ m with he_def
  have hcd : Commute c d := by rw [Commute, SemiconjBy, hdc]
  have he_idem : IsIdempotentElem e := by
    unfold IsIdempotentElem
    have h2 := key m
    calc e * e = c ^ m * (d ^ m * c ^ m) * d ^ m := by simp only [he_def, mul_assoc]
      _ = c ^ m * (c ^ m * d ^ m) * d ^ m := by rw [← (hcd.pow_pow m m).eq]
      _ = c ^ (m + m) * d ^ m * d ^ m := by rw [pow_add]; simp only [mul_assoc]
      _ = c ^ m * d ^ m := by rw [← h2]
  have he_mem : e ∈ Z := Z.mul_mem (Z.pow_mem hc m) (Z.pow_mem hd m)
  by_contra hne
  by_cases he0 : e = 0
  ·
    have hcm0 : c ^ m = 0 := by
      have h2 := key m
      rw [h2, pow_add, mul_assoc, ← he_def, he0, mul_zero]
    have hnil : IsNilpotent (⟨c, hc⟩ : Z) := ⟨m, Subtype.ext (by simpa using hcm0)⟩
    have := hZ.2
    have := hnil.eq_zero
    exact hne (by simpa using congrArg Subtype.val this)
  ·
    have hb : c ^ m * d ^ (m + 1) ∈ Z := Z.mul_mem (Z.pow_mem hc m) (Z.pow_mem hd _)
    have hbe : c ^ m * d ^ (m + 1) * c = e := by
      calc c ^ m * d ^ (m + 1) * c = c ^ m * (c * d ^ (m + 1)) := by
            rw [mul_assoc, ← (hcd.pow_right (m + 1)).eq]
        _ = c ^ (m + 1) * (d * d ^ m) := by rw [← mul_assoc, ← pow_succ, pow_succ' d m]
        _ = e := by rw [← mul_assoc, ← hmd]
    exact trace_ne_zero_of_idem he_idem he0 (by rw [← hbe]; exact h _ hb)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[qZ, mul_add, trace_add]`.
-/
theorem qZ_add (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x + y) = qZ Z x + qZ Z y := by
  funext i
  simp [qZ, mul_add, trace_add]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[qZ, mul_sub, trace_sub]`.
-/
theorem qZ_sub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (x y : Matrix (Fin n) (Fin n) k) :
    qZ Z (x - y) = qZ Z x - qZ Z y := by
  funext i
  simp [qZ, mul_sub, trace_sub]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `hb : ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) ∈ Z` using `(Module.finBasis k Z i).2`. Establish `hcomm : Commute ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) x` using `hx _ hb`. Use `Matrix.isNilpotent_trace_of_isNilpotent (hcomm.isNilpotent_mul_left hn)` as an intermediate fact. Simplify `this.eq_zero` using `[qZ]`.
-/
theorem qZ_nil (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hn : IsNilpotent x) : qZ Z x = 0 := by
  funext i
  have hb : ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) ∈ Z := (Module.finBasis k Z i).2
  have hcomm : Commute ((Module.finBasis k Z i : Z) : Matrix (Fin n) (Fin n) k) x := hx _ hb
  have := Matrix.isNilpotent_trace_of_isNilpotent (hcomm.isNilpotent_mul_left hn)
  simpa [qZ] using this.eq_zero

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Establish `h0 : qZ Z (c - c') = 0` using `by rw [qZ_sub, h, sub_self]`. Rewrite using `[← sub_eq_zero]`. Use `eq_zero_of_trace hZ (Z.sub_mem hc hc') fun b hb => ?_` and prove the remaining obligations. Set `ℓ : Z →ₗ[k] k` to `{ toFun := fun a => trace ((a : Matrix (Fin n) (Fin n) k) * (c - c')) map_add' := fun a b => by simp [add_mul, trace_add] map_smul' := fun a b => by simp [trace_smul] }`. Establish `hℓ : ℓ = 0` using `(Module.finBasis k Z).ext fun i => by`.

Use `congrFun h0 i` as an intermediate fact. Simplify `this` using `[qZ, ℓ]`. Conclude with `congrArg (fun f : Z →ₗ[k] k => f ⟨b, hb⟩) hℓ`.
-/
theorem qZ_inj [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) {c c' : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) (hc' : c' ∈ Z) (h : qZ Z c = qZ Z c') : c = c' := by
  have h0 : qZ Z (c - c') = 0 := by rw [qZ_sub, h, sub_self]
  rw [← sub_eq_zero]
  refine eq_zero_of_trace hZ (Z.sub_mem hc hc') fun b hb => ?_
  let ℓ : Z →ₗ[k] k :=
    { toFun := fun a => trace ((a : Matrix (Fin n) (Fin n) k) * (c - c'))
      map_add' := fun a b => by simp [add_mul, trace_add]
      map_smul' := fun a b => by simp [trace_smul] }
  have hℓ : ℓ = 0 := (Module.finBasis k Z).ext fun i => by
    have := congrFun h0 i
    simpa [qZ, ℓ] using this
  exact congrArg (fun f : Z →ₗ[k] k => f ⟨b, hb⟩) hℓ

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Set `φ : Z →ₗ[k] (Fin (Module.finrank k Z) → k)` to `{ toFun := fun c => qZ Z (c : Matrix (Fin n) (Fin n) k) map_add' := fun a b => qZ_add Z a b map_smul' := fun a b => by funext i; simp [qZ, trace_smul] }`. Establish `hinj : Function.Injective φ` using `fun a b h => Subtype.ext (qZ_inj hZ a.2 b.2 h)`. Establish `hsurj : Function.Surjective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj`. Take `⟨c, hc⟩` from `hsurj y`. Conclude with `⟨c, c.2, hc⟩`.
-/
theorem qZ_surj [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    (y : Fin (Module.finrank k Z) → k) : ∃ c ∈ Z, qZ Z c = y := by
  let φ : Z →ₗ[k] (Fin (Module.finrank k Z) → k) :=
    { toFun := fun c => qZ Z (c : Matrix (Fin n) (Fin n) k)
      map_add' := fun a b => qZ_add Z a b
      map_smul' := fun a b => by funext i; simp [qZ, trace_smul] }
  have hinj : Function.Injective φ := fun a b h => Subtype.ext (qZ_inj hZ a.2 b.2 h)
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp)).1 hinj
  obtain ⟨c, hc⟩ := hsurj y
  exact ⟨c, c.2, hc⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Establish `h : ∃ c ∈ Z, qZ Z c = qZ Z x` using `qZ_surj hZ _`. Unfold `piZ`. Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem piZ_spec [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z) (x : Matrix (Fin n) (Fin n) k) :
    piZ Z x ∈ Z ∧ qZ Z (piZ Z x) = qZ Z x := by
  have h : ∃ c ∈ Z, qZ Z c = qZ Z x := qZ_surj hZ _
  unfold piZ
  rw [dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Introduce `n Z hZ y`. Take `⟨c, hc, hcy⟩` from `qZ_surj hZ y`. Use `⟨c, hc, hcy, fun x hx => ⟨fun ⟨hqy, c', hc', hnil⟩ => ?_, fun hnil => ⟨?_, c, hc, hnil⟩⟩⟩` and prove the remaining obligations. Establish `hx' : x - c' ∈ Bz Z` using `fun a ha => by`. Rewrite using `[mul_sub, sub_mul, hx a ha, hZ.1 a ha c' hc']`.

Establish `h1 : qZ Z x = qZ Z c'`. Use `qZ_nil Z hx' hnil` as an intermediate fact. Rewrite `this` using `[qZ_sub, sub_eq_zero]`. Conclude with `this`. Establish `: c' = c` using `qZ_inj hZ hc' hc (by rw [← h1, hqy, hcy])`.

Rewrite `hnil` using `[this]`. Then use the resulting hypothesis. Establish `hx' : x - c ∈ Bz Z` using `fun a ha => by`. Rewrite using `[mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]`. Use `qZ_nil Z hx' hnil` as an intermediate fact. Rewrite `this` using `[qZ_sub, sub_eq_zero]`.

Rewrite using `[this, hcy]`.
-/
theorem fibZN [CharZero k] : FibZN (k := k) := by
  intro n Z hZ y
  obtain ⟨c, hc, hcy⟩ := qZ_surj hZ y
  refine ⟨c, hc, hcy, fun x hx => ⟨fun ⟨hqy, c', hc', hnil⟩ => ?_, fun hnil => ⟨?_, c, hc, hnil⟩⟩⟩
  · have hx' : x - c' ∈ Bz Z := fun a ha => by
      rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c' hc']
    have h1 : qZ Z x = qZ Z c' := by
      have := qZ_nil Z hx' hnil
      rw [qZ_sub, sub_eq_zero] at this
      exact this
    have : c' = c := qZ_inj hZ hc' hc (by rw [← h1, hqy, hcy])
    rwa [this] at hnil
  · have hx' : x - c ∈ Bz Z := fun a ha => by
      rw [mul_sub, sub_mul, hx a ha, hZ.1 a ha c hc]
    have := qZ_nil Z hx' hnil
    rw [qZ_sub, sub_eq_zero] at this
    rw [this, hcy]

end PositivityTheory.RgUd.T.Nil.Orb.Ofib
