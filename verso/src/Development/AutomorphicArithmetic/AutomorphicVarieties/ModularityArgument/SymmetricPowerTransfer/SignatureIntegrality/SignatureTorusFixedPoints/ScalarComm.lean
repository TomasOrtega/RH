import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.LevelTorusLeTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ConjDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.BdMul

noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym

namespace UpperTheory.V.Z.Sym.Sig

section Abs

open MulAction

/- English proof (translation)
Establish `key : ∀ o : orbitRel.Quotient T Y, f o.out ≠ 0 → o = Quotient.mk'' y₀` using `fun o ho => (Quotient.out_eq' o).symm.trans (Quotient.eq''.2 (hs _ ho).2)`. Use `⟨Set.Subsingleton.finite fun o ho o' ho' => (key o ho).trans (key o' ho').symm, ?_⟩` and prove the remaining obligations. Unfold `wcount`. Distinguish the cases in `hP : P`. Rewrite using `[if_pos hP, finsum_eq_single _ (Quotient.mk'' y₀)]`.

Establish `hm : (Quotient.mk'' y₀ : orbitRel.Quotient T Y).out ∈ orbit T y₀` using `orbitRel_apply.1 (Quotient.eq''.1 (Quotient.out_eq' _))`. Rewrite using `[ht _ hm, hv hP _ hm]`. Introduce `o ho`. Establish `h0 : f o.out = 0` using `by_contra fun h => ho (key o h)`. Simplify using `[h0]`.

Rewrite using `[if_neg hP]`. Establish `h0 : ∀ o : orbitRel.Quotient T Y, f o.out = 0` using `fun o => by_contra fun h => hP (hs _ h).1`. Simplify using `[h0]`.
-/
private theorem one_orbit {T Y : Type} [Group T] [MulAction T Y] (C S : Subgroup T) (f : Y → ℂ) (y₀ : Y) (c : ℂ)
    (P : Prop) [Decidable P] (hs : ∀ y, f y ≠ 0 → P ∧ y ∈ orbit T y₀) (hv : P → ∀ y ∈ orbit T y₀, f y = c)
    (ht : ∀ y ∈ orbit T y₀, stabilizer T y = S) :
    {o : orbitRel.Quotient T Y | f o.out ≠ 0}.Finite ∧
      wcount C f = if P then (S.relIndex C : ℂ) * c else 0 := by
  have key : ∀ o : orbitRel.Quotient T Y, f o.out ≠ 0 → o = Quotient.mk'' y₀ := fun o ho =>
    (Quotient.out_eq' o).symm.trans (Quotient.eq''.2 (hs _ ho).2)
  refine ⟨Set.Subsingleton.finite fun o ho o' ho' => (key o ho).trans (key o' ho').symm, ?_⟩
  unfold wcount
  by_cases hP : P
  · rw [if_pos hP, finsum_eq_single _ (Quotient.mk'' y₀)]
    · have hm : (Quotient.mk'' y₀ : orbitRel.Quotient T Y).out ∈ orbit T y₀ :=
        orbitRel_apply.1 (Quotient.eq''.1 (Quotient.out_eq' _))
      rw [ht _ hm, hv hP _ hm]
    · intro o ho
      have h0 : f o.out = 0 := by_contra fun h => ho (key o h)
      simp [h0]
  · rw [if_neg hP]
    have h0 : ∀ o : orbitRel.Quotient T Y, f o.out = 0 := fun o => by_contra fun h => hP (hs _ h).1
    simp [h0]

end Abs

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[val_diagT, Matrix.diagonal_apply, Matrix.one_apply, GeneralLinearGroup.scalar]`.
-/
private theorem scalar_eq {n : ℕ} (z : kˣ) : GeneralLinearGroup.scalar (Fin n) z = dg (fun _ => z) := by
  apply Units.ext
  ext i j
  simp [val_diagT, Matrix.diagonal_apply, Matrix.one_apply, GeneralLinearGroup.scalar]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[GeneralLinearGroup.scalar, mul_comm]`.
-/
private theorem scalar_comm {n : ℕ} (z : kˣ) (x : GL (Fin n) k) :
    GeneralLinearGroup.scalar (Fin n) z * x = x * GeneralLinearGroup.scalar (Fin n) z := by
  apply Units.ext
  ext i j
  simp [GeneralLinearGroup.scalar, mul_comm]

/- English proof (translation)
Rewrite using `[← mul_assoc, ← mul_assoc, h]`.
-/
private theorem conj_sc {G : Type} [Group G] (S j W : G) (h : S * j⁻¹ = j⁻¹ * S) :
    S * (j⁻¹ * W * j) = j⁻¹ * S * W * j := by
  rw [← mul_assoc, ← mul_assoc, h]

/- English proof (translation)
The claim follows from `map_mul _ _ _`.
-/
private theorem dg_mul {n : ℕ} (a b : Fin n → kˣ) : dg (a * b) = dg a * dg b := map_mul _ _ _

/- English proof (translation)
The claim follows from `map_inv _ _`.
-/
private theorem dg_inv {n : ℕ} (a : Fin n → kˣ) : dg a⁻¹ = (dg a)⁻¹ := map_inv _ _

/- English proof (translation)
Rewrite using `[← dg_mul, ← dg_mul, mul_comm]`.
-/
private theorem dg_comm {n : ℕ} (a b : Fin n → kˣ) : dg a * dg b = dg b * dg a := by
  rw [← dg_mul, ← dg_mul, mul_comm]

/- English proof (translation)
Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first | exact h | exact absurd hij (by decide)`.
-/
private theorem sdom2 {x : Fin 2 → kˣ} (h : valuation k (x 0 : k) < valuation k (x 1 : k)) : SDom x := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact h | exact absurd hij (by decide)

/- English proof (translation)
Establish `hz` using `(eqZ k V ω hω 2 (by norm_num)).2.1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨z, j, hj, e⟩` from `(hz _).1 h`. Establish `e1 : dg w = dg (fun _ => z) * j` using `by rw [e, scalar_eq]`.

Establish `e2 : j = dg ((fun _ => z)⁻¹ * w)`. Rewrite using `[dg_mul, dg_inv, e1, inv_mul_cancel_left]`. Establish `hm : ∀ i, ((fun _ => z)⁻¹ * w : Fin 2 → kˣ) i ∈ V.H`. Introduce `i`. Take `⟨u, hu, hu'⟩` from `((memJ k V 2 j).1 hj).2.2 i`.

Establish `: u = ((fun _ => z)⁻¹ * w : Fin 2 → kˣ) i`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hu', e2, dg, val_diagT, diagonal_apply_eq]`. Conclude with `this ▸ hu`. Use `div_mem (hm 0) (hm 1)` as an intermediate fact.

Simplify `this` using `[mul_div_mul_left_eq_div]`. Introduce `h`. Use `(hz _).2 ⟨w 1, dg ![w 0 / w 1, 1], V.dg_mem ?_, ?_⟩` and prove the remaining obligations. Introduce `i fin_cases i`. Conclude with `h`.

Conclude with `one_mem _`. Rewrite using `[scalar_eq, ← dg_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp`.
-/
private theorem dg_mem_ZJ (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) {w : Fin 2 → kˣ} :
    dg w ∈ V.ZJ 2 ↔ w 0 / w 1 ∈ V.H := by
  have hz := (eqZ k V ω hω 2 (by norm_num)).2.1
  constructor
  · intro h
    obtain ⟨z, j, hj, e⟩ := (hz _).1 h
    have e1 : dg w = dg (fun _ => z) * j := by rw [e, scalar_eq]
    have e2 : j = dg ((fun _ => z)⁻¹ * w) := by
      rw [dg_mul, dg_inv, e1, inv_mul_cancel_left]
    have hm : ∀ i, ((fun _ => z)⁻¹ * w : Fin 2 → kˣ) i ∈ V.H := by
      intro i
      obtain ⟨u, hu, hu'⟩ := ((memJ k V 2 j).1 hj).2.2 i
      have : u = ((fun _ => z)⁻¹ * w : Fin 2 → kˣ) i := by
        apply Units.ext
        rw [hu', e2, dg, val_diagT, diagonal_apply_eq]
      exact this ▸ hu
    have := div_mem (hm 0) (hm 1)
    simpa [mul_div_mul_left_eq_div] using this
  · intro h
    refine (hz _).2 ⟨w 1, dg ![w 0 / w 1, 1], V.dg_mem ?_, ?_⟩
    · intro i
      fin_cases i
      · exact h
      · exact one_mem _
    · rw [scalar_eq, ← dg_mul]
      congr 1
      funext i
      fin_cases i <;> simp

/- English proof (translation)
Establish `hex : ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g) ∈ V.DC d`. Assume the negation of the conclusion as `hn`. Conclude with `h (by rw [Lev.fZ, dif_neg hn])`. Take `⟨z, hz⟩` from `hex`. Take `⟨j, hj, s, ⟨s', hs', rfl⟩, e⟩` from `contract k V 2 (MonoidHom.id _) (pres_id V 2) d hd _ hz`.

Establish `hs : ∀ i, s' i ∈ V.H` using `fun i => hs' i trivial`. Establish `e' : j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g)) * j = dg s' * dg d` using `e`. Establish `hc` using `scalar_comm z j⁻¹`. Establish `e3 : (g₀⁻¹ * g * j)⁻¹ * dg ![a, b] * (g₀⁻¹ * g * j) = dg ((fun _ => z) * s' * d)`. Rewrite using `[dg_mul, dg_mul, mul_assoc (dg fun _ => z), ← e', ← scalar_eq, conj_sc _ _ _ hc]`.

Use `group`. Establish `hv : ∀ i, valuation k (s' i : k) = 1` using `fun i => V.H_le (hs i)`. Establish `hzpos : 0 < valuation k (z : k)` using `zero_lt_iff.2 (by simp)`. Establish `hsd : SDom ((fun _ => z) * s' * d)` using `sdom2 (by`. Simplify using `only [Pi.mul_apply, Units.val_mul, map_mul, hv, mul_one]`.

Conclude with `mul_lt_mul_of_pos_left (hd 0 1 (by decide)) hzpos)`. Take `⟨E, u, hu⟩` from `conjDiag k 2 ![a, b] _ (sdom2 hab) hsd _ e3`. Establish `ha : a = z * s' 0 * d 0` using `congrFun E 0`. Establish `hb : b = z * s' 1 * d 1` using `congrFun E 1`. Use `⟨?_, u, j⁻¹, inv_mem hj, ?_⟩` and prove the remaining obligations.

Establish `: a / b / (d 0 / d 1) = s' 0 / s' 1`. Rewrite using `[ha, hb, mul_assoc z, mul_assoc z, mul_div_mul_left_eq_div, mul_div_mul_comm, mul_div_cancel_right]`. Rewrite using `[this]`. Conclude with `div_mem (hs 0) (hs 1)`. Rewrite using `[← hu] group`.
-/
private theorem supp_orb (V : Lev k) (ω : kˣ →* ℂˣ) (d : Fin 2 → kˣ) (hd : SDom d) (g₀ : GL (Fin 2) k) (a b : kˣ)
    (hab : valuation k (a : k) < valuation k (b : k)) (g : GL (Fin 2) k)
    (h : V.fZ ω d (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g) ≠ 0) :
    a / b / (d 0 / d 1) ∈ V.H ∧ ∃ u : Fin 2 → kˣ, ∃ j ∈ V.J 2, g = g₀ * dg u * j := by
  have hex : ∃ z : kˣ, (GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g) ∈ V.DC d := by
    by_contra hn
    exact h (by rw [Lev.fZ, dif_neg hn])
  obtain ⟨z, hz⟩ := hex
  obtain ⟨j, hj, s, ⟨s', hs', rfl⟩, e⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) d hd _ hz
  have hs : ∀ i, s' i ∈ V.H := fun i => hs' i trivial
  have e' : j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z)⁻¹ * (g⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * g)) * j = dg s' * dg d := e
  have hc := scalar_comm z j⁻¹
  have e3 : (g₀⁻¹ * g * j)⁻¹ * dg ![a, b] * (g₀⁻¹ * g * j) = dg ((fun _ => z) * s' * d) := by
    rw [dg_mul, dg_mul, mul_assoc (dg fun _ => z), ← e', ← scalar_eq, conj_sc _ _ _ hc]
    group
  have hv : ∀ i, valuation k (s' i : k) = 1 := fun i => V.H_le (hs i)
  have hzpos : 0 < valuation k (z : k) := zero_lt_iff.2 (by simp)
  have hsd : SDom ((fun _ => z) * s' * d) := sdom2 (by
    simp only [Pi.mul_apply, Units.val_mul, map_mul, hv, mul_one]
    exact mul_lt_mul_of_pos_left (hd 0 1 (by decide)) hzpos)
  obtain ⟨E, u, hu⟩ := conjDiag k 2 ![a, b] _ (sdom2 hab) hsd _ e3
  have ha : a = z * s' 0 * d 0 := congrFun E 0
  have hb : b = z * s' 1 * d 1 := congrFun E 1
  refine ⟨?_, u, j⁻¹, inv_mem hj, ?_⟩
  · have : a / b / (d 0 / d 1) = s' 0 / s' 1 := by
      rw [ha, hb, mul_assoc z, mul_assoc z, mul_div_mul_left_eq_div, mul_div_mul_comm, mul_div_cancel_right]
    rw [this]
    exact div_mem (hs 0) (hs 1)
  · rw [← hu]
    group

/- English proof (translation)
Establish `hE` using `eqZ k V ω hω 2 (by norm_num)`. Take `⟨z', j, hj, rfl⟩` from `(hE.2.1 v).1 hv`. Establish `hD : dg ![a, b] = GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (dg ![a / b / (d 0 / d 1), 1] * dg d)`. Rewrite using `[scalar_eq, ← dg_mul, ← dg_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Apply `Units.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts.

Simplify using the standard rewrite rules. Establish `hX : (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j))⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j)) = GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (j⁻¹ * dg ![a / b / (d 0 / d 1), 1] * dg d * j)`. Establish `h1 : (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j))⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j)) = j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z')⁻¹ * ((dg u)⁻¹ * dg ![a, b] * dg u) * GeneralLinearGroup.scalar (Fin 2) z') * j` using `by group`. Establish `h2 : (dg u)⁻¹ * dg ![a, b] * dg u = dg ![a, b]`. Rewrite using `[mul_assoc, dg_comm ![a, b] u, inv_mul_cancel_left]`.

Establish `h3 : (GeneralLinearGroup.scalar (Fin 2) z')⁻¹ * dg ![a, b] * GeneralLinearGroup.scalar (Fin 2) z' = dg ![a, b]`. Rewrite using `[mul_assoc, ← scalar_comm, inv_mul_cancel_left]`. Rewrite using `[h1, h2, h3, hD, mul_assoc j⁻¹ (dg ![a / b / (d 0 / d 1), 1]) (dg d), conj_sc _ _ _ (scalar_comm _ j⁻¹)]`. Use `group`. Rewrite using `[hX, hE.2.2 d hd |>.1 _ _ ⟨j⁻¹ * dg ![a / b / (d 0 / d 1), 1], mul_mem (inv_mem hj) (V.dg_mem ?_), j, hj, rfl⟩, ← map_inv, inv_div]`.

Introduce `i`. Use `fin_cases i`. Conclude with `hc`. Conclude with `one_mem _`.
-/
private theorem value_orb (V : Lev k) (ω : kˣ →* ℂˣ) (hω : ∀ u ∈ V.H, ω u = 1) (d : Fin 2 → kˣ) (hd : SDom d)
    (g₀ : GL (Fin 2) k) (a b : kˣ) (hc : a / b / (d 0 / d 1) ∈ V.H) (u : Fin 2 → kˣ) (v : GL (Fin 2) k)
    (hv : v ∈ V.ZJ 2) :
    V.fZ ω d ((g₀ * dg u * v)⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * (g₀ * dg u * v)) = (ω (d 1 / b) : ℂ) := by
  have hE := eqZ k V ω hω 2 (by norm_num)
  obtain ⟨z', j, hj, rfl⟩ := (hE.2.1 v).1 hv
  have hD : dg ![a, b] = GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (dg ![a / b / (d 0 / d 1), 1] * dg d) := by
    rw [scalar_eq, ← dg_mul, ← dg_mul]
    congr 1
    funext i
    fin_cases i
    · apply Units.ext
      simp
      field_simp
    · simp
  have hX : (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j))⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) *
      (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j)) =
      GeneralLinearGroup.scalar (Fin 2) (b / d 1) * (j⁻¹ * dg ![a / b / (d 0 / d 1), 1] * dg d * j) := by
    have h1 : (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j))⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) *
        (g₀ * dg u * (GeneralLinearGroup.scalar (Fin 2) z' * j)) =
        j⁻¹ * ((GeneralLinearGroup.scalar (Fin 2) z')⁻¹ * ((dg u)⁻¹ * dg ![a, b] * dg u) *
          GeneralLinearGroup.scalar (Fin 2) z') * j := by group
    have h2 : (dg u)⁻¹ * dg ![a, b] * dg u = dg ![a, b] := by
      rw [mul_assoc, dg_comm ![a, b] u, inv_mul_cancel_left]
    have h3 : (GeneralLinearGroup.scalar (Fin 2) z')⁻¹ * dg ![a, b] * GeneralLinearGroup.scalar (Fin 2) z' = dg ![a, b] := by
      rw [mul_assoc, ← scalar_comm, inv_mul_cancel_left]
    rw [h1, h2, h3, hD, mul_assoc j⁻¹ (dg ![a / b / (d 0 / d 1), 1]) (dg d), conj_sc _ _ _ (scalar_comm _ j⁻¹)]
    group
  rw [hX, hE.2.2 d hd |>.1 _ _ ⟨j⁻¹ * dg ![a / b / (d 0 / d 1), 1], mul_mem (inv_mem hj) (V.dg_mem ?_), j, hj, rfl⟩,
    ← map_inv, inv_div]
  intro i
  fin_cases i
  · exact hc
  · exact one_mem _

/- English proof (translation)
Introduce `k _ _ _ _ V ω hω d hd T _ p q hpq g₀ ι hι a b hab`. Use `letI : MulAction T (GL (Fin 2) k ⧸ V.ZJ 2) := MulAction.compHom _ ι`. Establish `hJ : V.J 2 ≤ V.ZJ 2` using `le_sup_right`. Establish `hrel : (V.H.comap (p / q)).relIndex ((Uo k).comap (p / q)) = V.H.relIndex (Uo k)`. Rewrite using `[Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hpq]`.

Establish `horb : ∀ y ∈ MulAction.orbit T ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2), ∃ u : Fin 2 → kˣ, y = ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)`. Introduce and unpack `_ ⟨s, rfl⟩`. Use `⟨![p s, q s], ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((ι s * g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _`. Rewrite using `[hι]`.

Use `congr 1`. Use `group`. Establish `horb' : ∀ u : Fin 2 → kˣ, ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) ∈ MulAction.orbit T ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)`. Introduce `u`. Take `⟨s, hs⟩` from `hpq (u 0 / u 1)`.

Use `⟨s, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((ι s * g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _`. Rewrite using `[QuotientGroup.eq, hι]`. Establish `e : (g₀ * dg ![p s, q s] * g₀⁻¹ * g₀)⁻¹ * (g₀ * dg u) = dg (![p s, q s]⁻¹ * u)`. Rewrite using `[dg_mul, dg_inv]`.

Use `group`. Rewrite using `[e, dg_mem_ZJ V ω hω]`. Establish `hs' : p s / q s = u 0 / u 1` using `hs`. Establish `: (![p s, q s]⁻¹ * u) 0 / (![p s, q s]⁻¹ * u) 1 = 1`. Simplify using `only [Pi.mul_apply, Pi.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]`.

Rewrite using `[mul_div_mul_comm, ← hs']`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `one_mem _`. Establish `main` using `one_orbit ((Uo k).comap (p / q)) (V.H.comap (p / q)) (fun y : GL (Fin 2) k ⧸ V.ZJ 2 => V.fZ ω d (y.out⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * y.out)) ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) (ω (d 1 / b) : ℂ) (a / b / (d 0 / d 1) ∈ V.H) (by`.

Introduce `y hy`. Take `⟨hP, u, j, hj, e⟩` from `supp_orb V ω d hd g₀ a b hab _ hy`. Use `⟨hP, ?_⟩` and prove the remaining obligations. Establish `: y = ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)`. Rewrite using `[← QuotientGroup.out_eq' y, e]`.

Conclude with `QuotientGroup.mk_mul_of_mem _ (hJ hj)`. Conclude with `this ▸ horb' u)`. Use the proof step `(by`. Introduce `hP y hy`. Take `⟨u, rfl⟩` from `horb y hy`.

Establish `hm : (g₀ * dg u)⁻¹ * (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out ∈ V.ZJ 2` using `QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm`. Establish `e : (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out = g₀ * dg u * ((g₀ * dg u)⁻¹ * (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out)` using `by group`. Use `show V.fZ ω d _ = _`. Rewrite using `[e]`. Conclude with `value_orb V ω hω d hd g₀ a b hP u _ hm)`.

Use the proof step `(by`. Introduce `y hy`. Take `⟨u, rfl⟩` from `horb y hy`. Use extensionality with `s`. Rewrite using `[MulAction.mem_stabilizer_iff, Subgroup.mem_comap, MonoidHom.div_apply]`.

Express the relevant statement in the definitionally equal form `((ι s * (g₀ * dg u) : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _ ↔ _`. Rewrite using `[QuotientGroup.eq, hι]`. Establish `e : (g₀ * dg ![p s, q s] * g₀⁻¹ * (g₀ * dg u))⁻¹ * (g₀ * dg u) = dg ![p s, q s]⁻¹`. Rewrite using `[dg_inv]`. Establish `: g₀ * dg ![p s, q s] * g₀⁻¹ * (g₀ * dg u) = g₀ * dg u * dg ![p s, q s]`.

Rewrite using `[mul_assoc g₀ (dg u), dg_comm u]`. Use `group`. Rewrite using `[this]`. Use `group`. Rewrite using `[e, dg_mem_ZJ V ω hω]`.

Establish `: (![p s, q s]⁻¹ : Fin 2 → kˣ) 0 / (![p s, q s]⁻¹ : Fin 2 → kˣ) 1 = (p s / q s)⁻¹`. Simplify using the standard rewrite rules. Rewrite using `[div_eq_mul_inv, mul_comm]`. Rewrite using `[this, inv_mem_iff])`. Rewrite `main` using `[hrel]`.

Use `⟨main.1, ?_⟩` and prove the remaining obligations. Unfold `orb`. Conclude with `main.2`.
-/
theorem orbZ : OrbZ := by
  classical
  intro k _ _ _ _ V ω hω d hd T _ p q hpq g₀ ι hι a b hab
  letI : MulAction T (GL (Fin 2) k ⧸ V.ZJ 2) := MulAction.compHom _ ι
  have hJ : V.J 2 ≤ V.ZJ 2 := le_sup_right
  have hrel : (V.H.comap (p / q)).relIndex ((Uo k).comap (p / q)) = V.H.relIndex (Uo k) := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hpq]
  have horb : ∀ y ∈ MulAction.orbit T ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2),
      ∃ u : Fin 2 → kˣ, y = ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
    rintro _ ⟨s, rfl⟩
    refine ⟨![p s, q s], ?_⟩
    change ((ι s * g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _
    rw [hι]
    congr 1
    group
  have horb' : ∀ u : Fin 2 → kˣ, ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) ∈
      MulAction.orbit T ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
    intro u
    obtain ⟨s, hs⟩ := hpq (u 0 / u 1)
    refine ⟨s, ?_⟩
    change ((ι s * g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _
    rw [QuotientGroup.eq, hι]
    have e : (g₀ * dg ![p s, q s] * g₀⁻¹ * g₀)⁻¹ * (g₀ * dg u) = dg (![p s, q s]⁻¹ * u) := by
      rw [dg_mul, dg_inv]
      group
    rw [e, dg_mem_ZJ V ω hω]
    have hs' : p s / q s = u 0 / u 1 := hs
    have : (![p s, q s]⁻¹ * u) 0 / (![p s, q s]⁻¹ * u) 1 = 1 := by
      simp only [Pi.mul_apply, Pi.inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [mul_div_mul_comm, ← hs']
      simp
    rw [this]
    exact one_mem _
  have main := one_orbit ((Uo k).comap (p / q)) (V.H.comap (p / q))
    (fun y : GL (Fin 2) k ⧸ V.ZJ 2 => V.fZ ω d (y.out⁻¹ * (g₀ * dg ![a, b] * g₀⁻¹) * y.out))
    ((g₀ : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) (ω (d 1 / b) : ℂ) (a / b / (d 0 / d 1) ∈ V.H)
    (by
      intro y hy
      obtain ⟨hP, u, j, hj, e⟩ := supp_orb V ω d hd g₀ a b hab _ hy
      refine ⟨hP, ?_⟩
      have : y = ((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) := by
        rw [← QuotientGroup.out_eq' y, e]
        exact QuotientGroup.mk_mul_of_mem _ (hJ hj)
      exact this ▸ horb' u)
    (by
      intro hP y hy
      obtain ⟨u, rfl⟩ := horb y hy
      have hm : (g₀ * dg u)⁻¹ * (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out ∈ V.ZJ 2 :=
        QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm
      have e : (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out =
          g₀ * dg u * ((g₀ * dg u)⁻¹ * (((g₀ * dg u : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2)).out) := by
        group
      show V.fZ ω d _ = _
      rw [e]
      exact value_orb V ω hω d hd g₀ a b hP u _ hm)
    (by
      intro y hy
      obtain ⟨u, rfl⟩ := horb y hy
      ext s
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, MonoidHom.div_apply]
      change ((ι s * (g₀ * dg u) : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.ZJ 2) = _ ↔ _
      rw [QuotientGroup.eq, hι]
      have e : (g₀ * dg ![p s, q s] * g₀⁻¹ * (g₀ * dg u))⁻¹ * (g₀ * dg u) = dg ![p s, q s]⁻¹ := by
        rw [dg_inv]
        have : g₀ * dg ![p s, q s] * g₀⁻¹ * (g₀ * dg u) = g₀ * dg u * dg ![p s, q s] := by
          rw [mul_assoc g₀ (dg u), dg_comm u]
          group
        rw [this]
        group
      rw [e, dg_mem_ZJ V ω hω]
      have : (![p s, q s]⁻¹ : Fin 2 → kˣ) 0 / (![p s, q s]⁻¹ : Fin 2 → kˣ) 1 = (p s / q s)⁻¹ := by
        simp
        rw [div_eq_mul_inv, mul_comm]
      rw [this, inv_mem_iff])
  rw [hrel] at main
  refine ⟨main.1, ?_⟩
  unfold orb
  exact main.2

end UpperTheory.V.Z.Sym.Sig

end
