import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.DiagDC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym.Sig

local notation "S[" n "]" => GeneralLinearGroup.scalar (Fin n)

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[dg, val_diagT, GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply]`.
-/
private theorem sc_eq (z : kˣ) : S[n] z = dg (fun _ : Fin n => z) := by
  apply Units.ext
  ext i j
  simp [dg, val_diagT, GeneralLinearGroup.scalar, Matrix.diagonal_apply, Matrix.one_apply]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_mul, Units.val_mul, sc_eq, dg, val_diagT]`. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]`.
-/
private theorem sc_comm (z : kˣ) (g : GL (Fin n) k) : S[n] z * g = g * S[n] z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, sc_eq, dg, val_diagT]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨u, hu, e⟩` from `((memJ k V n _).1 h).2.2 ⟨0, hn⟩`. Establish `: u = z`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[e, sc_eq, dg, val_diagT]`. Simplify using the standard rewrite rules. Conclude with `this ▸ hu`. Introduce `h`. Rewrite using `[sc_eq]`.

Conclude with `le_sup_left (b := (glIwa k n).Nm V.c) (le_sup_right (a := (glIwa k n).N) ⟨fun _ => z, fun _ _ => h, rfl⟩)`.
-/
private theorem sc_mem_iff (V : Lev k) (hn : 0 < n) (z : kˣ) : S[n] z ∈ V.J n ↔ z ∈ V.H := by
  constructor
  · intro h
    obtain ⟨u, hu, e⟩ := ((memJ k V n _).1 h).2.2 ⟨0, hn⟩
    have : u = z := by
      apply Units.ext
      rw [e, sc_eq, dg, val_diagT]
      simp
    exact this ▸ hu
  · intro h
    rw [sc_eq]
    exact le_sup_left (b := (glIwa k n).Nm V.c) (le_sup_right (a := (glIwa k n).N) ⟨fun _ => z, fun _ _ => h, rfl⟩)

/- English proof (translation)
Introduce `i j h` and use `h.eq_or_lt.elim (fun e => by rw [e]) (fun l => (hd i j l).le)`.
-/
private theorem dom_of (d : Fin n → kˣ) (hd : SDom d) : Dom d := fun i j h =>
  h.eq_or_lt.elim (fun e => by rw [e]) (fun l => (hd i j l).le)

/- English proof (translation)
Take `⟨j, hj, _, ⟨t, ht, rfl⟩, e⟩` from `contract k V n (MonoidHom.id _) (pres_id V n) d hd g hg`. Take `⟨a, ha, b, hb, e2⟩` from `h`. Establish `e3 : dg ((fun _ => z) * t * d) = (j⁻¹ * a) * dg d * (b * j)`. Establish `e4 : dg ((fun _ => z) * t * d) = S[n] z * (diagT k (Fin n) t * dg d)`. Rewrite using `[sc_eq, dg, dg, dg, map_mul, map_mul, mul_assoc]`.

Rewrite using `[e4, ← e, MonoidHom.id_apply]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← mul_assoc, sc_comm z j⁻¹]`. Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [e2]; group`.

Establish `h1 : dg ((fun _ => z) * t * d) ∈ V.DC d` using `⟨_, mul_mem (inv_mem hj) ha, _, mul_mem hb hj, e3⟩`. Establish `h2` using `(diagDC k V n d _ (dom_of d hd)).1 h1 ⟨0, hn⟩`. Establish `h3 : z * t ⟨0, hn⟩ * d ⟨0, hn⟩ / d ⟨0, hn⟩ ∈ V.H` using `h2`. Establish `h4` using `div_mem h3 (ht ⟨0, hn⟩ trivial)`. Simplify using `using h4`.
-/
private theorem H_of_mem (V : Lev k) (hn : 0 < n) {d : Fin n → kˣ} (hd : SDom d) {g : GL (Fin n) k}
    (hg : g ∈ V.DC d) {z : kˣ} (h : S[n] z * g ∈ V.DC d) : z ∈ V.H := by
  obtain ⟨j, hj, _, ⟨t, ht, rfl⟩, e⟩ := contract k V n (MonoidHom.id _) (pres_id V n) d hd g hg
  obtain ⟨a, ha, b, hb, e2⟩ := h
  have e3 : dg ((fun _ => z) * t * d) = (j⁻¹ * a) * dg d * (b * j) := by
    have e4 : dg ((fun _ => z) * t * d) = S[n] z * (diagT k (Fin n) t * dg d) := by
      rw [sc_eq, dg, dg, dg, map_mul, map_mul, mul_assoc]
    rw [e4, ← e, MonoidHom.id_apply]
    calc S[n] z * (j⁻¹ * g * j) = j⁻¹ * (S[n] z * g) * j := by
          rw [← mul_assoc, ← mul_assoc, sc_comm z j⁻¹]; simp only [mul_assoc]
      _ = _ := by rw [e2]; group
  have h1 : dg ((fun _ => z) * t * d) ∈ V.DC d := ⟨_, mul_mem (inv_mem hj) ha, _, mul_mem hb hj, e3⟩
  have h2 := (diagDC k V n d _ (dom_of d hd)).1 h1 ⟨0, hn⟩
  have h3 : z * t ⟨0, hn⟩ * d ⟨0, hn⟩ / d ⟨0, hn⟩ ∈ V.H := h2
  have h4 := div_mem h3 (ht ⟨0, hn⟩ trivial)
  simpa using h4

/- English proof (translation)
Use `haveI : (S[n] : kˣ →* GL (Fin n) k).range.Normal := ⟨by`. Introduce and unpack `_ ⟨z, rfl⟩ g`. Conclude with `⟨z, by rw [← sc_comm z g]; simp⟩⟩`. Rewrite using `[← SetLike.mem_coe, Lev.ZJ, Subgroup.normal_mul, Set.mem_mul]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨z, rfl⟩, j, hj, rfl⟩`. Conclude with `⟨z, j, hj, rfl⟩`. Introduce and unpack `⟨z, j, hj, rfl⟩`. Conclude with `⟨_, ⟨z, rfl⟩, j, hj, rfl⟩`.
-/
private theorem mem_ZJ (V : Lev k) (u : GL (Fin n) k) :
    u ∈ V.ZJ n ↔ ∃ z : kˣ, ∃ j ∈ V.J n, u = S[n] z * j := by
  haveI : (S[n] : kˣ →* GL (Fin n) k).range.Normal := ⟨by
    rintro _ ⟨z, rfl⟩ g
    exact ⟨z, by rw [← sc_comm z g]; simp⟩⟩
  rw [← SetLike.mem_coe, Lev.ZJ, Subgroup.normal_mul, Set.mem_mul]
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩
    exact ⟨z, j, hj, rfl⟩
  · rintro ⟨z, j, hj, rfl⟩
    exact ⟨_, ⟨z, rfl⟩, j, hj, rfl⟩

/- English proof (translation)
Establish `hex : ∃ z : kˣ, (S[n] z)⁻¹ * g ∈ V.DC d` using `⟨z, h⟩`. Rewrite using `[Lev.fZ, dif_pos hex]`. Establish `hc` using `hex.choose_spec`. Generalize the expression as in `hex.choose = c at hc ⊢`. Establish `h1 : z / c ∈ V.H` using `H_of_mem V hn hd h (g := (S[n] z)⁻¹ * g) (by`.

Use `hc using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_div, div_eq_mul_inv, map_mul, map_inv]`. Rewrite using `[sc_comm z, ← mul_assoc, mul_assoc _ _ g]`. Use the proof step `group)`. Establish `h2` using `hω _ h1`.

Rewrite `h2` using `[map_div, div_eq_one]`. Rewrite using `[h2]`.
-/
private theorem fZ_eq (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) (hn : 0 < n)
    {d : Fin n → kˣ} (hd : SDom d) {z : kˣ} {g : GL (Fin n) k} (h : (S[n] z)⁻¹ * g ∈ V.DC d) :
    V.fZ ω d g = (((ω z)⁻¹ : ℂˣ) : ℂ) := by
  have hex : ∃ z : kˣ, (S[n] z)⁻¹ * g ∈ V.DC d := ⟨z, h⟩
  rw [Lev.fZ, dif_pos hex]
  have hc := hex.choose_spec
  generalize hex.choose = c at hc ⊢
  have h1 : z / c ∈ V.H := H_of_mem V hn hd h (g := (S[n] z)⁻¹ * g) (by
    convert hc using 1
    simp only [map_div, div_eq_mul_inv, map_mul, map_inv]
    rw [sc_comm z, ← mul_assoc, mul_assoc _ _ g]
    group)
  have h2 := hω _ h1
  rw [map_div, div_eq_one] at h2
  rw [h2]

/- English proof (translation)
Take `⟨a, ha, b, hb, e⟩` from `h`. Use `⟨u * a, mul_mem hu ha, b * u', mul_mem hb hu', ?_⟩` and prove the remaining obligations. Establish `: (S[n] c)⁻¹ * (u * g * u') = u * ((S[n] c)⁻¹ * g) * u'`. Rewrite using `[← map_inv, ← mul_assoc, ← mul_assoc, sc_comm c⁻¹ u]`. Simplify using `only [mul_assoc]`.

Rewrite using `[this, e]`. Use `group`.
-/
private theorem dc_tr (V : Lev k) {d : Fin n → kˣ} {c : kˣ} {g u u' : GL (Fin n) k}
    (hu : u ∈ V.J n) (hu' : u' ∈ V.J n) (h : (S[n] c)⁻¹ * g ∈ V.DC d) :
    (S[n] c)⁻¹ * (u * g * u') ∈ V.DC d := by
  obtain ⟨a, ha, b, hb, e⟩ := h
  refine ⟨u * a, mul_mem hu ha, b * u', mul_mem hb hu', ?_⟩
  have : (S[n] c)⁻¹ * (u * g * u') = u * ((S[n] c)⁻¹ * g) * u' := by
    rw [← map_inv, ← mul_assoc, ← mul_assoc, sc_comm c⁻¹ u]; simp only [mul_assoc]
  rw [this, e]; group

end

/- English proof (translation)
Introduce `k _ _ _ _ V ω hω n hn`. Establish `wd : ∀ (z z' : kˣ) (j j' : GL (Fin n) k), j ∈ V.J n → j' ∈ V.J n → S[n] z * j = S[n] z' * j' → ω z = ω z'`. Introduce `z z' j j' hj hj' e`. Establish `h1 : S[n] (z'⁻¹ * z) = j' * j⁻¹`. Rewrite using `[map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]`.

Use `group`. Establish `h2 : z'⁻¹ * z ∈ V.H` using `(sc_mem_iff V hn _).1 (h1 ▸ mul_mem hj' (inv_mem hj))`. Establish `h3` using `hω _ h2`. Rewrite `h3` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h3.symm`.

Establish `hZ : ∀ u : V.ZJ n, ∃ z : kˣ, ∃ j ∈ V.J n, (u : GL (Fin n) k) = S[n] z * j` using `fun u => (mem_ZJ V u.1).1 u.2`. Use `choose Z Jf hJ eZ using hZ`. Use `⟨⟨MonoidHom.mk' (fun u => ω (Z u)) ?_, ?_⟩, mem_ZJ V, ?_⟩` and prove the remaining obligations. Introduce `u v`. Rewrite using `[← map_mul]`.

Use `wd _ _ _ _ (hJ (u * v)) (mul_mem (hJ u) (hJ v)) ?_` and prove the remaining obligations. Rewrite using `[← eZ (u * v), Subgroup.coe_mul, eZ u, eZ v, map_mul, mul_assoc, mul_assoc, ← mul_assoc (Jf u), ← sc_comm, mul_assoc]`. Introduce `z j u hj e`. Conclude with `wd _ _ _ _ (hJ u) hj ((eZ u).symm.trans e)`. Introduce `d hd`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z g hg`. Conclude with `fZ_eq V ω hω hn hd (by rwa [inv_mul_cancel_left])`. Introduce `z g`. Distinguish the cases in `h : ∃ c : kˣ, (S[n] c)⁻¹ * g ∈ V.DC d`.

Take `⟨c, hc⟩` from `h`. Rewrite using `[fZ_eq V ω hω hn hd hc, fZ_eq V ω hω hn hd (z := z * c) (by`. Use `hc using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul]`. Use the proof step `group), map_mul, mul_inv, Units.val_mul]`.

Establish `h0 : V.fZ ω d g = 0` using `dif_neg h`. Establish `h1 : V.fZ ω d (S[n] z * g) = 0` using `dif_neg (fun ⟨c, hc⟩ => h ⟨z⁻¹ * c, by`. Use `hc using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul, map_inv]`. Use the proof step `group⟩)`.

Rewrite using `[h0, h1, mul_zero]`. Introduce `u hu u' hu' g`. Distinguish the cases in `h : ∃ c : kˣ, (S[n] c)⁻¹ * g ∈ V.DC d`. Take `⟨c, hc⟩` from `h`. Rewrite using `[fZ_eq V ω hω hn hd hc, fZ_eq V ω hω hn hd (dc_tr V hu hu' hc)]`.

Establish `h0 : V.fZ ω d g = 0` using `dif_neg h`. Establish `h1 : V.fZ ω d (u * g * u') = 0` using `dif_neg (fun ⟨c, hc⟩ => h ⟨c, by`. Establish `h2` using `dc_tr V (inv_mem hu) (inv_mem hu') hc`. Establish `e : u⁻¹ * (u * g * u') * u'⁻¹ = g` using `by group`. Rewrite using `[e] at h2⟩)` and apply the resulting hypothesis.

Rewrite using `[h0, h1]`. Establish `hfin` using `((finFacts k V).2.2.2.2.2 n).1 (dg d)`. Use `(Set.Finite.image (fun q : GL (Fin n) k ⧸ V.J n => ((q.out : GL (Fin n) k) : GL (Fin n) k ⧸ V.ZJ n)) hfin).subset ?_` and prove the remaining obligations. Introduce `y hy`. Establish `hex : ∃ c : kˣ, (S[n] c)⁻¹ * y.out ∈ V.DC d`.

Assume the negation of the conclusion as `h`. Conclude with `hy (dif_neg h)`. Take `⟨c, a, ha, b, hb, e⟩` from `hex`. Take `⟨j, hj⟩` from `QuotientGroup.mk_out_eq_mul (V.J n) (a * dg d)`. Use `⟨((a * dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n), ⟨⟨a, ha⟩, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show ((((a * dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n).out : GL (Fin n) k) : GL (Fin n) k ⧸ V.ZJ n) = y`. Establish `e1 : y.out = (a * dg d) * (S[n] c * b)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hj, ← QuotientGroup.out_eq' y, QuotientGroup.eq, e1]`. Use `(mem_ZJ V _).2 ⟨c, (j : GL (Fin n) k)⁻¹ * b, mul_mem (inv_mem j.2) hb, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.Z.Sym.Sig.eqZ :
    UpperTheory.V.Z.Sym.Sig.EqZ := by
  intro k _ _ _ _ V ω hω n hn
  have wd : ∀ (z z' : kˣ) (j j' : GL (Fin n) k), j ∈ V.J n → j' ∈ V.J n →
      S[n] z * j = S[n] z' * j' → ω z = ω z' := by
    intro z z' j j' hj hj' e
    have h1 : S[n] (z'⁻¹ * z) = j' * j⁻¹ := by
      rw [map_mul, map_inv, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← e]
      group
    have h2 : z'⁻¹ * z ∈ V.H := (sc_mem_iff V hn _).1 (h1 ▸ mul_mem hj' (inv_mem hj))
    have h3 := hω _ h2
    rw [map_mul, map_inv, inv_mul_eq_one] at h3
    exact h3.symm
  have hZ : ∀ u : V.ZJ n, ∃ z : kˣ, ∃ j ∈ V.J n, (u : GL (Fin n) k) = S[n] z * j :=
    fun u => (mem_ZJ V u.1).1 u.2
  choose Z Jf hJ eZ using hZ
  refine ⟨⟨MonoidHom.mk' (fun u => ω (Z u)) ?_, ?_⟩, mem_ZJ V, ?_⟩
  · intro u v
    rw [← map_mul]
    refine wd _ _ _ _ (hJ (u * v)) (mul_mem (hJ u) (hJ v)) ?_
    rw [← eZ (u * v), Subgroup.coe_mul, eZ u, eZ v, map_mul, mul_assoc, mul_assoc,
      ← mul_assoc (Jf u), ← sc_comm, mul_assoc]
  · intro z j u hj e
    exact wd _ _ _ _ (hJ u) hj ((eZ u).symm.trans e)
  · intro d hd
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z g hg
      exact fZ_eq V ω hω hn hd (by rwa [inv_mul_cancel_left])
    · intro z g
      by_cases h : ∃ c : kˣ, (S[n] c)⁻¹ * g ∈ V.DC d
      · obtain ⟨c, hc⟩ := h
        rw [fZ_eq V ω hω hn hd hc, fZ_eq V ω hω hn hd (z := z * c) (by
          convert hc using 1
          rw [map_mul]
          group), map_mul, mul_inv, Units.val_mul]
      · have h0 : V.fZ ω d g = 0 := dif_neg h
        have h1 : V.fZ ω d (S[n] z * g) = 0 := dif_neg (fun ⟨c, hc⟩ => h ⟨z⁻¹ * c, by
          convert hc using 1
          rw [map_mul, map_inv]
          group⟩)
        rw [h0, h1, mul_zero]
    · intro u hu u' hu' g
      by_cases h : ∃ c : kˣ, (S[n] c)⁻¹ * g ∈ V.DC d
      · obtain ⟨c, hc⟩ := h
        rw [fZ_eq V ω hω hn hd hc, fZ_eq V ω hω hn hd (dc_tr V hu hu' hc)]
      · have h0 : V.fZ ω d g = 0 := dif_neg h
        have h1 : V.fZ ω d (u * g * u') = 0 := dif_neg (fun ⟨c, hc⟩ => h ⟨c, by
          have h2 := dc_tr V (inv_mem hu) (inv_mem hu') hc
          have e : u⁻¹ * (u * g * u') * u'⁻¹ = g := by group
          rwa [e] at h2⟩)
        rw [h0, h1]
    · have hfin := ((finFacts k V).2.2.2.2.2 n).1 (dg d)
      refine (Set.Finite.image (fun q : GL (Fin n) k ⧸ V.J n =>
        ((q.out : GL (Fin n) k) : GL (Fin n) k ⧸ V.ZJ n)) hfin).subset ?_
      intro y hy
      have hex : ∃ c : kˣ, (S[n] c)⁻¹ * y.out ∈ V.DC d := by
        by_contra h
        exact hy (dif_neg h)
      obtain ⟨c, a, ha, b, hb, e⟩ := hex
      obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul (V.J n) (a * dg d)
      refine ⟨((a * dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n), ⟨⟨a, ha⟩, rfl⟩, ?_⟩
      show ((((a * dg d : GL (Fin n) k) : GL (Fin n) k ⧸ V.J n).out : GL (Fin n) k) : GL (Fin n) k ⧸ V.ZJ n) = y
      have e1 : y.out = (a * dg d) * (S[n] c * b) := by
        calc y.out = S[n] c * ((S[n] c)⁻¹ * y.out) := by group
          _ = S[n] c * (a * dg d * b) := by rw [e]
          _ = _ := by rw [← mul_assoc, sc_comm c (a * dg d), mul_assoc]
      rw [hj, ← QuotientGroup.out_eq' y, QuotientGroup.eq, e1]
      refine (mem_ZJ V _).2 ⟨c, (j : GL (Fin n) k)⁻¹ * b, mul_mem (inv_mem j.2) hb, ?_⟩
      calc (a * dg d * (j : GL (Fin n) k))⁻¹ * (a * dg d * (S[n] c * b))
          = (j : GL (Fin n) k)⁻¹ * S[n] c * b := by group
        _ = _ := by rw [← sc_comm, mul_assoc]

end
