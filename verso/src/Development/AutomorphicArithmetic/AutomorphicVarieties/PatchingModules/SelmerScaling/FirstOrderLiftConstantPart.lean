import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.FirstOrderMatrixMemSquareZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EOneTranspose
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlSel
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ConjConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InvEv
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.KapF

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {g n : ℕ}

private def aH (X : Type) [CommRing X] (g : ℕ) : DD X g →+ X where
  toFun u := u.a
  map_zero' := rfl
  map_add' _ _ := rfl

private def epH (X : Type) [CommRing X] {g : ℕ} (j : Fin g) : DD X g →+ X where
  toFun u := u.ep j
  map_zero' := rfl
  map_add' _ _ := rfl

/- English proof (translation)
The claim follows from `map_sum (aH X g) f s`.
-/
private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (aH X g) f s

/- English proof (translation)
The claim follows from `map_sum (epH X m) f s`.
-/
private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (m : Fin g) :
    (∑ i ∈ s, f i).ep m = ∑ i ∈ s, (f i).ep m :=
  map_sum (epH X m) f s

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem sub_a (u v : DD X g) : (u - v).a = u.a - v.a := by
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem sub_ep (u v : DD X g) (m : Fin g) : (u - v).ep m = u.ep m - v.ep m := by
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem smul_a (c : X) (u : DD X g) : (c • u).a = c * u.a := rfl

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Use `show _ = _`. Simplify using `[DD.instAlgebra]`. Rewrite using `[RingHom.algebraMap_toAlgebra]`. Simplify using `[DD.C]`.

Express the relevant statement in the definitionally equal form `c * u.ep m + (0 : Fin g → X) m * u.a = c * u.ep m`. Simplify using the standard rewrite rules.
-/
private theorem smul_ep (c : X) (u : DD X g) (m : Fin g) : (c • u).ep m = c * u.ep m := by
  rw [Algebra.smul_def]
  show _ = _
  simp [DD.instAlgebra]
  rw [RingHom.algebraMap_toAlgebra]
  simp [DD.C]
  change c * u.ep m + (0 : Fin g → X) m * u.a = c * u.ep m
  simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, sum_a]`. Both sides reduce to the same expression.
-/
private theorem mul_mapa (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map (fun u => u.a) = P.map (fun u => u.a) * Q.map (fun u => u.a) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, sum_a]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, sum_ep, ← Finset.sum_add_distrib]`. Both sides reduce to the same expression.
-/
private theorem mul_mapep (P Q : Matrix (Fin n) (Fin n) (DD X g)) (m : Fin g) :
    (P * Q).map (fun u => u.ep m) =
      P.map (fun u => u.a) * Q.map (fun u => u.ep m) + P.map (fun u => u.ep m) * Q.map (fun u => u.a) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, sum_ep, ← Finset.sum_add_distrib]
  rfl

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[sub_a]`.
-/
private theorem sub_mapa (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P - Q).map (fun u => u.a) = P.map (fun u => u.a) - Q.map (fun u => u.a) := by
  ext a b
  simp [sub_a]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[sub_ep]`.
-/
private theorem sub_mapep (P Q : Matrix (Fin n) (Fin n) (DD X g)) (m : Fin g) :
    (P - Q).map (fun u => u.ep m) = P.map (fun u => u.ep m) - Q.map (fun u => u.ep m) := by
  ext a b
  simp [sub_ep]

end SlopeTestRemainingChoices

/- English proof (translation)
Unfold `Kap.ρ1`. Rewrite using `[mul_mapa]`. Establish `h1 : (1 + DD.epM fun j => (k.κ j γ).map (algebraMap x.A X)).map (fun u : DD X k.g => u.a) = (1 : Matrix (Fin n) (Fin n) X)`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.add_apply]`.

Express the relevant statement in the definitionally equal form `((1 : Matrix (Fin n) (Fin n) (DD X k.g)) i j).a + 0 = (1 : Matrix (Fin n) (Fin n) X) i j`. Rewrite using `[add_zero, Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Establish `h2 : (x.ρX (DD X k.g) γ).map (fun u => u.a) = x.ρX X γ`. Use extensionality with `i j`. Both sides reduce to the same expression. Rewrite using `[h1, h2, one_mul]`.
-/
private theorem first_order_lift_constant_part {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X]
    [Algebra x.A X] (γ : F.G₀) : (k.ρ1 X γ).map (fun u => u.a) = x.ρX X γ := by
  unfold Kap.ρ1
  rw [mul_mapa]
  have h1 : (1 + DD.epM fun j => (k.κ j γ).map (algebraMap x.A X)).map (fun u : DD X k.g => u.a) =
      (1 : Matrix (Fin n) (Fin n) X) := by
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply]
    change ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) i j).a + 0 = (1 : Matrix (Fin n) (Fin n) X) i j
    rw [add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  have h2 : (x.ρX (DD X k.g) γ).map (fun u => u.a) = x.ρX X γ := by
    ext i j
    rfl
  rw [h1, h2, one_mul]

end UpperTheory.V.Pa

/- English proof (translation)
Set `q` to `Fintype.equivFin ι`. Use `hK _ (fun j => z (q.symm j)) (fun j => hz _) ?_` and prove the remaining obligations. Introduce `c hc`. Establish `h0 : (fun i => c (q i)) = 0`. Apply `hind` to reduce the goal to its premises.

Establish `hs : ∑ i, c (q i) • z i = ∑ j, c j • z (q.symm j)`. Rewrite using `[← Equiv.sum_comp q (fun j => c j • z (q.symm j))]`. Simplify using the standard rewrite rules. Rewrite using `[hs]`. Conclude with `hc`.

Use function extensionality and compare the values at `j`. Use `congrFun h0 (q.symm j)` as an intermediate fact. Simplify using `using this`.
-/
private theorem card_le_of_linearIndependent_mod_bd1_in_sel1 {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ}
    {x : NP G0.frame n} (k : Kap x) (D0 : ℕ) (hK : SelmerRankBoundLaurent h k D0) {ι : Type} [Fintype ι]
    (z : ι → G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g))
    (hz : ∀ i, z i ∈ Sel1 h x.Fr k ∧ BndD x.t (z i))
    (hind : ∀ c : ι → x.Fr, ∑ i, c i • z i ∈ Bd1 h x.Fr k → c = 0) : Fintype.card ι ≤ D0 := by
  let q := Fintype.equivFin ι
  refine hK _ (fun j => z (q.symm j)) (fun j => hz _) ?_
  intro c hc
  have h0 : (fun i => c (q i)) = 0 := by
    apply hind
    have hs : ∑ i, c (q i) • z i = ∑ j, c j • z (q.symm j) := by
      rw [← Equiv.sum_comp q (fun j => c j • z (q.symm j))]
      simp
    rw [hs]
    exact hc
  funext j
  have := congrFun h0 (q.symm j)
  simpa using this

/- English proof (translation)
Rewrite using `[sub_mapa, mul_mapa, mul_mapa, first_order_lift_constant_part, first_order_lift_constant_part]`.
-/
private theorem map_a_rho1_mul_mul_sub_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (γ δ : F.G₀) (Y : Matrix (Fin n) (Fin n) (DD X k.g)) :
    (k.ρ1 X γ * Y * k.ρ1 X δ - Y).map (fun u => u.a) =
      x.ρX X γ * Y.map (fun u => u.a) * x.ρX X δ - Y.map (fun u => u.a) := by
  rw [sub_mapa, mul_mapa, mul_mapa, first_order_lift_constant_part, first_order_lift_constant_part]

/- English proof (translation)
Rewrite using `[sub_mapep, mul_mapep, mul_mapep, mul_mapa, hY, first_order_lift_constant_part, first_order_lift_constant_part]`. Simplify using the standard rewrite rules.
-/
private theorem map_ep_rho1_mul_mul_sub_eq_of_map_a_eq_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (γ δ : F.G₀) (Y : Matrix (Fin n) (Fin n) (DD X k.g)) (m : Fin k.g)
    (hY : Y.map (fun u => u.a) = 0) :
    (k.ρ1 X γ * Y * k.ρ1 X δ - Y).map (fun u => u.ep m) =
      x.ρX X γ * Y.map (fun u => u.ep m) * x.ρX X δ - Y.map (fun u => u.ep m) := by
  rw [sub_mapep, mul_mapep, mul_mapep, mul_mapa, hY, first_order_lift_constant_part, first_order_lift_constant_part]
  simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_a_add_of_commRing {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) : (u + v).a = u.a + v.a := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem dd_ep_add_apply {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) (m : Fin g) :
    (u + v).ep m = u.ep m + v.ep m := rfl

/- English proof (translation)
Introduce `l _ S D0 hK e α hα hl`. Establish `hsel : ∀ i, S.alC (α i) ∈ SelP S.h S.x S.F ∧ BndM S.x.t (S.alC (α i))` using `fun i => (alSel l S).1 _ (α i).2`. Use `choose y hy1 hy2 hy3 using fun i => lift1 l S.L S.G S.G0 S.h S.n S.x S.k _ (hsel i).1 (hsel i).2 (hl i)`. Establish `hy4 : ∀ i γ a b, (y i γ a b).a = S.alC (α i) γ a b`. Introduce `i γ a b`.

Rewrite using `[← hy3]`. Both sides reduce to the same expression. Set `w : Fin S.k.g × Fin S.k.g → S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.x.Fr S.k.g)` to `fun p γ => DD.epM (Pi.single p.2 (kapF S.h S.k p.1 γ))`. Establish `hw0 : ∀ p γ a b, (w p γ a b).a = 0` using `fun _ _ _ _ => rfl`. Set `z : Fin e ⊕ (Fin S.k.g × Fin S.k.g) → S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.x.Fr S.k.g)` to `Sum.elim y w`.

Establish `hz : ∀ i, z i ∈ Sel1 S.h S.x.Fr S.k ∧ BndD S.x.t (z i)`. Introduce and unpack `(i | p)`. Conclude with `⟨hy1 i, hy2 i⟩`. Conclude with `kapSel1 l S.L S.G S.G0 S.h S.n S.x S.k p.1 p.2`. Establish `hind : ∀ c : Fin e ⊕ (Fin S.k.g × Fin S.k.g) → S.x.Fr, ∑ i, c i • z i ∈ Bd1 S.h S.x.Fr S.k → c = 0`.

Introduce `c hc`. Take `⟨Y, hYW, hYt, hYeq⟩` from `hc`. Establish `hsum : ∑ i, c i • z i = ∑ i, c (Sum.inl i) • y i + ∑ p, c (Sum.inr p) • w p`. Rewrite using `[Fintype.sum_sum_type]`. Both sides reduce to the same expression.

Rewrite `hYeq` using `[hsum]`. Establish `hA : ∀ γ, (∑ i, c (Sum.inl i) • S.alC (α i)) γ = S.x.ρX S.x.Fr (S.h.p₀ γ) * Y.map (fun u => u.a) * S.x.ρX S.x.Fr (S.h.p₀ γ⁻¹) - Y.map (fun u => u.a)`. Introduce `γ`. Establish `e1` using `congrArg (fun M => M.map (fun u : DD S.x.Fr S.k.g => u.a)) (congrFun hYeq γ)`. Simplify using `only [dY] at e1`.

Rewrite `e1` using `[map_a_rho1_mul_mul_sub_eq]`. Rewrite using `[← e1]`. Use extensionality with `a b`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, dd_a_add_of_commRing, sum_a, smul_a, hy4, hw0, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero]`. Establish `hnegA : ∀ u : DD S.x.Fr S.k.g, (-u).a = -u.a` using `fun u => map_neg (aH S.x.Fr S.k.g) u`.

Establish `hTA : (Y.map (fun u => u.a))ᵀ = -(Y.map (fun u => u.a))`. Rewrite using `[← Matrix.transpose_map, hYt]`. Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.neg_apply, hnegA]`. Establish `hEv : Y.map (fun u => u.a) ∈ Ev S.x.A S.x.Fr S.n S.x.a`.

Introduce `a b`. Use `⟨fun _ => Submodule.mem_top, fun hab => ?_⟩` and prove the remaining obligations. Establish `h1` using `((hYW a b).2 hab).1 rfl`. Conclude with `(Submodule.mem_bot _).2 h1`. Establish `hmem : ∑ i, c (Sum.inl i) • (α i : S.Bh →+ S.F) ∈ S.Tp` using `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (α i).2)`.

Establish `hBd : S.alC (∑ i, c (Sum.inl i) • (α i : S.Bh →+ S.F)) ∈ BdP S.h S.x S.F`. Rewrite using `[(alSel l S).2.2.1 (Fin e) (fun i => c (Sum.inl i)) (fun i => (α i : S.Bh →+ S.F))]`. Use `⟨Y.map (fun u => u.a), hEv, hTA, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `γ`. Conclude with `hA γ`.

Establish `hz0` using `alInj l S _ hmem hBd`. Establish `hc1 : ∀ i, c (Sum.inl i) = 0`. Use `Fintype.linearIndependent_iff.1 hα (fun i => c (Sum.inl i)) ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`.

Simplify using `using hz0`. Establish `hYa : Y.map (fun u => u.a) = 0`. Use `invEv l S.L S.G S.G0 S.h S.n S.x S.odd _ hEv hTA ?_` and prove the remaining obligations. Introduce `γ`. Simplify using `only [dY]`.

Rewrite using `[← hA γ]`. Simplify using `[hc1]`. Establish `hEp : ∀ m : Fin S.k.g, ∀ γ, (∑ i, c (Sum.inr (i, m)) • kapF S.h S.k i) γ = S.x.ρX S.x.Fr (S.h.p₀ γ) * Y.map (fun u => u.ep m) * S.x.ρX S.x.Fr (S.h.p₀ γ⁻¹) - Y.map (fun u => u.ep m)`. Introduce `m γ`. Establish `e1` using `congrArg (fun M => M.map (fun u : DD S.x.Fr S.k.g => u.ep m)) (congrFun hYeq γ)`.

Simplify using `only [dY] at e1`. Rewrite `e1` using `[map_ep_rho1_mul_mul_sub_eq_of_map_a_eq_zero _ _ _ _ _ _ hYa]`. Rewrite using `[← e1]`. Use extensionality with `a b`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.map_apply, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, dd_ep_add_apply, sum_ep, smul_ep, hc1, zero_mul, Finset.sum_const_zero, zero_add, smul_eq_mul]`.

Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Establish `hw : ∀ j, (w (i, j) γ a b).ep m = if m = j then kapF S.h S.k i γ a b else 0`. Introduce `j`. Use `show (Pi.single j (kapF S.h S.k i γ) : Fin S.k.g → _) m a b = _`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Both sides reduce to the same expression. Both sides reduce to the same expression. Simplify using `only [hw, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.

Establish `hd : ∀ m, (fun i => c (Sum.inr (i, m))) = 0`. Introduce `m`. Establish `hnegE : ∀ u : DD S.x.Fr S.k.g, (-u).ep m = -u.ep m` using `fun u => map_neg (epH S.x.Fr m) u`. Apply `indF l S.L S.G S.G0 S.h S.n S.x S.k` to reduce the goal to its premises. Use `⟨Y.map (fun u => u.ep m), ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `a b`. Use `⟨fun hab => ?_, fun _ => Submodule.mem_top⟩` and prove the remaining obligations. Establish `h1` using `((hYW a b).1 hab).2.1 rfl`. Conclude with `(Submodule.mem_bot _).2 (congrFun h1 m)`. Rewrite using `[← Matrix.transpose_map, hYt]`.

Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.neg_apply, hnegE]`. Use function extensionality and compare the values at `γ`. Conclude with `hEp m γ`. Use function extensionality and compare the values at `s`.

Break down `s with i | p` into its components or cases. Conclude with `hc1 i`. Conclude with `congrFun (hd p.2) p.1`. Use `card_le_of_linearIndependent_mod_bd1_in_sel1 S.h S.k D0 hK z hz hind` as an intermediate fact. Simplify using `using this`.
-/
theorem UpperTheory.V.Pa.claim1 :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ D0, SelmerRankBoundLaurent S.h S.k D0 → ∀ (e : ℕ) (α : Fin e → S.Tp), LinearIndependent S.F α → (∀ i j, Lifts S.h S.k (Pi.single j (S.alC (α i)))) → e + S.k.g * S.k.g ≤ D0 := by
  intro l _ S D0 hK e α hα hl
  classical
  have hsel : ∀ i, S.alC (α i) ∈ SelP S.h S.x S.F ∧ BndM S.x.t (S.alC (α i)) :=
    fun i => (alSel l S).1 _ (α i).2
  choose y hy1 hy2 hy3 using fun i => lift1 l S.L S.G S.G0 S.h S.n S.x S.k _ (hsel i).1 (hsel i).2 (hl i)
  have hy4 : ∀ i γ a b, (y i γ a b).a = S.alC (α i) γ a b := by
    intro i γ a b
    rw [← hy3]
    rfl
  let w : Fin S.k.g × Fin S.k.g → S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.x.Fr S.k.g) :=
    fun p γ => DD.epM (Pi.single p.2 (kapF S.h S.k p.1 γ))
  have hw0 : ∀ p γ a b, (w p γ a b).a = 0 := fun _ _ _ _ => rfl
  let z : Fin e ⊕ (Fin S.k.g × Fin S.k.g) → S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.x.Fr S.k.g) :=
    Sum.elim y w
  have hz : ∀ i, z i ∈ Sel1 S.h S.x.Fr S.k ∧ BndD S.x.t (z i) := by
    rintro (i | p)
    · exact ⟨hy1 i, hy2 i⟩
    · exact kapSel1 l S.L S.G S.G0 S.h S.n S.x S.k p.1 p.2
  have hind : ∀ c : Fin e ⊕ (Fin S.k.g × Fin S.k.g) → S.x.Fr,
      ∑ i, c i • z i ∈ Bd1 S.h S.x.Fr S.k → c = 0 := by
    intro c hc
    obtain ⟨Y, hYW, hYt, hYeq⟩ := hc
    have hsum : ∑ i, c i • z i = ∑ i, c (Sum.inl i) • y i + ∑ p, c (Sum.inr p) • w p := by
      rw [Fintype.sum_sum_type]
      rfl
    rw [hsum] at hYeq
    have hA : ∀ γ, (∑ i, c (Sum.inl i) • S.alC (α i)) γ =
        S.x.ρX S.x.Fr (S.h.p₀ γ) * Y.map (fun u => u.a) * S.x.ρX S.x.Fr (S.h.p₀ γ⁻¹) -
          Y.map (fun u => u.a) := by
      intro γ
      have e1 := congrArg (fun M => M.map (fun u : DD S.x.Fr S.k.g => u.a)) (congrFun hYeq γ)
      simp only [dY] at e1
      rw [map_a_rho1_mul_mul_sub_eq] at e1
      rw [← e1]
      ext a b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
        Matrix.sum_apply, Matrix.smul_apply, dd_a_add_of_commRing, sum_a, smul_a, hy4, hw0, smul_eq_mul, mul_zero,
        Finset.sum_const_zero, add_zero]
    have hnegA : ∀ u : DD S.x.Fr S.k.g, (-u).a = -u.a := fun u => map_neg (aH S.x.Fr S.k.g) u
    have hTA : (Y.map (fun u => u.a))ᵀ = -(Y.map (fun u => u.a)) := by
      rw [← Matrix.transpose_map, hYt]
      ext a b
      simp only [Matrix.map_apply, Matrix.neg_apply, hnegA]
    have hEv : Y.map (fun u => u.a) ∈ Ev S.x.A S.x.Fr S.n S.x.a := by
      intro a b
      refine ⟨fun _ => Submodule.mem_top, fun hab => ?_⟩
      have h1 := ((hYW a b).2 hab).1 rfl
      exact (Submodule.mem_bot _).2 h1
    have hmem : ∑ i, c (Sum.inl i) • (α i : S.Bh →+ S.F) ∈ S.Tp :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (α i).2)
    have hBd : S.alC (∑ i, c (Sum.inl i) • (α i : S.Bh →+ S.F)) ∈ BdP S.h S.x S.F := by
      rw [(alSel l S).2.2.1 (Fin e) (fun i => c (Sum.inl i)) (fun i => (α i : S.Bh →+ S.F))]
      refine ⟨Y.map (fun u => u.a), hEv, hTA, ?_⟩
      funext γ
      exact hA γ
    have hz0 := alInj l S _ hmem hBd
    have hc1 : ∀ i, c (Sum.inl i) = 0 := by
      refine Fintype.linearIndependent_iff.1 hα (fun i => c (Sum.inl i)) ?_
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa using hz0
    have hYa : Y.map (fun u => u.a) = 0 := by
      refine invEv l S.L S.G S.G0 S.h S.n S.x S.odd _ hEv hTA ?_
      intro γ
      simp only [dY]
      rw [← hA γ]
      simp [hc1]
    have hEp : ∀ m : Fin S.k.g, ∀ γ, (∑ i, c (Sum.inr (i, m)) • kapF S.h S.k i) γ =
        S.x.ρX S.x.Fr (S.h.p₀ γ) * Y.map (fun u => u.ep m) * S.x.ρX S.x.Fr (S.h.p₀ γ⁻¹) -
          Y.map (fun u => u.ep m) := by
      intro m γ
      have e1 := congrArg (fun M => M.map (fun u : DD S.x.Fr S.k.g => u.ep m)) (congrFun hYeq γ)
      simp only [dY] at e1
      rw [map_ep_rho1_mul_mul_sub_eq_of_map_a_eq_zero _ _ _ _ _ _ hYa] at e1
      rw [← e1]
      ext a b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
        Matrix.sum_apply, Matrix.smul_apply, dd_ep_add_apply, sum_ep, smul_ep, hc1, zero_mul,
        Finset.sum_const_zero, zero_add, smul_eq_mul]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hw : ∀ j, (w (i, j) γ a b).ep m = if m = j then kapF S.h S.k i γ a b else 0 := by
        intro j
        show (Pi.single j (kapF S.h S.k i γ) : Fin S.k.g → _) m a b = _
        rw [Pi.single_apply]
        split_ifs
        · rfl
        · rfl
      simp only [hw, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hd : ∀ m, (fun i => c (Sum.inr (i, m))) = 0 := by
      intro m
      have hnegE : ∀ u : DD S.x.Fr S.k.g, (-u).ep m = -u.ep m := fun u => map_neg (epH S.x.Fr m) u
      apply indF l S.L S.G S.G0 S.h S.n S.x S.k
      refine ⟨Y.map (fun u => u.ep m), ?_, ?_, ?_⟩
      · intro a b
        refine ⟨fun hab => ?_, fun _ => Submodule.mem_top⟩
        have h1 := ((hYW a b).1 hab).2.1 rfl
        exact (Submodule.mem_bot _).2 (congrFun h1 m)
      · rw [← Matrix.transpose_map, hYt]
        ext a b
        simp only [Matrix.map_apply, Matrix.neg_apply, hnegE]
      · funext γ
        exact hEp m γ
    funext s
    rcases s with i | p
    · exact hc1 i
    · exact congrFun (hd p.2) p.1
  have := card_le_of_linearIndependent_mod_bd1_in_sel1 S.h S.k D0 hK z hz hind
  simpa using this
