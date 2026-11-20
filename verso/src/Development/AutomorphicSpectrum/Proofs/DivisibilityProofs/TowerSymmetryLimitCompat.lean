import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MonomialLinesPermutationStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Top.PermInv

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => exact ⟨Fin.elim0, by simp⟩`. Consider the case `cons a s ih`. Take `⟨w, hw⟩` from `ih`. Rewrite using `[Multiset.card_cons]`.

Use `⟨Fin.cons a w, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `[hw, Multiset.singleton_add]`.
-/
theorem exists_word_multiset {α : Type} (s : Multiset α) :
    ∃ w : Fin (Multiset.card s) → α, ∑ k, ({w k} : Multiset α) = s := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    obtain ⟨w, hw⟩ := ih
    rw [Multiset.card_cons]
    refine ⟨Fin.cons a w, ?_⟩
    rw [Fin.sum_univ_succ]
    simp [hw, Multiset.singleton_add]

/- English proof (translation)
Rewrite using `[Finsupp.card_toMultiset]`. Both sides reduce to the same expression.
-/
theorem degree_eq_card {α : Type} (μ : α →₀ ℕ) : μ.degree = Multiset.card (Finsupp.toMultiset μ) := by
  rw [Finsupp.card_toMultiset]
  rfl

/- English proof (translation)
Substitute `h` using the available equality. Establish `hc : Multiset.card (Finsupp.toMultiset μ) = μ.degree` using `(degree_eq_card μ).symm`. Take `⟨w, hw⟩` from `exists_word_multiset (Finsupp.toMultiset μ)`. Use `⟨fun k => w (Fin.cast hc.symm k), ?_⟩` and prove the remaining obligations. Establish `H : Finsupp.toMultiset (∑ k, Finsupp.single (w (Fin.cast hc.symm k)) 1) = Finsupp.toMultiset μ`.

Rewrite using `[map_sum]`. Simplify using `only [Finsupp.toMultiset_single, one_smul]`. Conclude with `(Fintype.sum_equiv (finCongr hc.symm) _ _ (fun k => rfl)).trans hw`. Simplify `congrArg Multiset.toFinsupp H` using `[Finsupp.toMultiset_toFinsupp]`.
-/
theorem exists_word {α : Type} (μ : α →₀ ℕ) (d : ℕ) (h : μ.degree = d) :
    ∃ w : Fin d → α, ∑ k, Finsupp.single (w k) 1 = μ := by
  subst h
  have hc : Multiset.card (Finsupp.toMultiset μ) = μ.degree := (degree_eq_card μ).symm
  obtain ⟨w, hw⟩ := exists_word_multiset (Finsupp.toMultiset μ)
  refine ⟨fun k => w (Fin.cast hc.symm k), ?_⟩
  classical
  have H : Finsupp.toMultiset (∑ k, Finsupp.single (w (Fin.cast hc.symm k)) 1) = Finsupp.toMultiset μ := by
    rw [map_sum]
    simp only [Finsupp.toMultiset_single, one_smul]
    exact (Fintype.sum_equiv (finCongr hc.symm) _ _ (fun k => rfl)).trans hw
  simpa [Finsupp.toMultiset_toFinsupp] using congrArg Multiset.toFinsupp H

/- English proof (translation)
Rewrite using `[degree_eq_card, degree_eq_card, ← Finsupp.toMultiset_map, Multiset.card_map]`.
-/
theorem degree_mapDomain {α β : Type} (f : α → β) (μ : α →₀ ℕ) :
    (Finsupp.mapDomain f μ).degree = μ.degree := by
  rw [degree_eq_card, degree_eq_card, ← Finsupp.toMultiset_map, Multiset.card_map]

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

/- English proof (translation)
Establish `e : Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1) = ∑ k, Finsupp.single (some (w k)) (1 : ℕ)`. Simplify using `[Finsupp.mapDomain_finsetSum]`. Take `⟨hdeg, -, -, hv⟩` from `GlobalTheory.T.monomial_lines_permutation II hII M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) (fun k => some (w k)) M.arith (by rintro (_ | r); exacts [M.A_smooth, M.x_smooth t r])`. Establish `hnone : (∑ k, Finsupp.single (some (w k)) (1 : ℕ) : Option (Ψ × Fin N) →₀ ℕ) none = 0`. Simplify using `[Finsupp.finsetSum_apply]`.

Rewrite using `[e, RootModel.arMono, if_pos hdeg, hnone, pow_zero, mul_one, hv]`. Both sides reduce to the same expression.
-/
theorem arMono_word (M : RootModel Ψ N) (II : IntersectionSystem) (hII : IsIntersectionSystem II) (t : ℝ)
    (w : Fin (dimFl Ψ N + 1) → Ψ × Fin N) :
    M.arMono II t (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1)) =
      II _ _ M.P _ (fun j => M.x t (w j)) / (M.δ : ℝ) := by
  have e : Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1) =
      ∑ k, Finsupp.single (some (w k)) (1 : ℕ) := by
    simp [Finsupp.mapDomain_finsetSum]
  obtain ⟨hdeg, -, -, hv⟩ := GlobalTheory.T.monomial_lines_permutation II hII M.K M.ι M.P (dimFl Ψ N + 1) _ (M.line t) (fun k => some (w k))
    M.arith (by rintro (_ | r); exacts [M.A_smooth, M.x_smooth t r])
  have hnone : (∑ k, Finsupp.single (some (w k)) (1 : ℕ) : Option (Ψ × Fin N) →₀ ℕ) none = 0 := by
    simp [Finsupp.finsetSum_apply]
  rw [e, RootModel.arMono, if_pos hdeg, hnone, pow_zero, mul_one, hv]
  rfl

end GlobalTheory.CompanionTheory.Ar.Top.PermInv

namespace GlobalTheory.CompanionTheory.Ar.Top.PermInv

/- English proof (translation)
Distinguish the cases in `hd : μ.degree = dimFl Ψ N + 1`. Take `⟨w, rfl⟩` from `exists_word μ _ hd`. Establish `e : Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1) = ∑ k, Finsupp.single (σ (w k).1, (w k).2) (1 : ℕ)`. Simplify using `[Finsupp.mapDomain_finsetSum]`. Establish `hf : (fun t => M.arMono II t (Finsupp.mapDomain some (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1)))) = fun t => II _ _ M.P _ (fun j => M.x t (σ (w j).1, (w j).2)) / (M.δ : ℝ)`.

Use function extensionality and compare the values at `t`. Rewrite using `[e]`. Conclude with `arMono_word M II hII t (fun k => (σ (w k).1, (w k).2))`. Establish `hg : (fun t => M'.arMono II t (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1))) = fun t => II _ _ M'.P _ (fun j => M'.x t (w j)) / (M'.δ : ℝ)`. Use function extensionality and compare the values at `t`.

Conclude with `arMono_word M' II hII t w`. Take `⟨L1, h1⟩` from `hM (Finsupp.mapDomain some (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1)))`. Take `⟨L2, h2⟩` from `hM' (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1))`. Rewrite using `[h1.limUnder_eq, h2.limUnder_eq]`. Rewrite `h1` using `[hf]`.

Rewrite `h2` using `[hg]`. Conclude with `sub_eq_zero.1 (tendsto_nhds_unique (h1.sub h2) (hlim w))`. Establish `h0 : ∀ (K : RootModel Ψ N) (m : Ψ × Fin N →₀ ℕ), m.degree = μ.degree → (fun t => K.arMono II t (Finsupp.mapDomain some m)) = fun _ => 0`. Introduce `K m hm`. Use function extensionality and compare the values at `t`.

Rewrite using `[RootModel.arMono, if_neg (by rw [degree_mapDomain, hm]; exact hd)]`. Rewrite using `[h0 M _ (degree_mapDomain _ μ), h0 M' μ rfl]`.
-/
theorem limUnder_arMono_perm {Ψ : Type} [Fintype Ψ] {N : ℕ} (M M' : RootModel Ψ N) (II : IntersectionSystem)
    (hII : IsIntersectionSystem II) (hM : M.Converges II) (hM' : M'.Converges II) (σ : Equiv.Perm Ψ)
    (hlim : ∀ w : Fin (dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M.P _ (fun j => M.x t (σ (w j).1, (w j).2)) /
      (M.δ : ℝ) - II _ _ M'.P _ (fun j => M'.x t (w j)) / (M'.δ : ℝ)) (𝓝[>] 0) (𝓝 0))
    (μ : Ψ × Fin N →₀ ℕ) :
    (limUnder (𝓝[>] (0 : ℝ)) fun t => M.arMono II t
        (Finsupp.mapDomain some (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) μ))) =
      limUnder (𝓝[>] (0 : ℝ)) fun t => M'.arMono II t (Finsupp.mapDomain some μ) := by
  by_cases hd : μ.degree = dimFl Ψ N + 1
  · obtain ⟨w, rfl⟩ := exists_word μ _ hd
    have e : Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1) =
        ∑ k, Finsupp.single (σ (w k).1, (w k).2) (1 : ℕ) := by
      simp [Finsupp.mapDomain_finsetSum]
    have hf : (fun t => M.arMono II t (Finsupp.mapDomain some
        (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1)))) =
        fun t => II _ _ M.P _ (fun j => M.x t (σ (w j).1, (w j).2)) / (M.δ : ℝ) := by
      funext t
      rw [e]
      exact arMono_word M II hII t (fun k => (σ (w k).1, (w k).2))
    have hg : (fun t => M'.arMono II t (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1))) =
        fun t => II _ _ M'.P _ (fun j => M'.x t (w j)) / (M'.δ : ℝ) := by
      funext t
      exact arMono_word M' II hII t w
    obtain ⟨L1, h1⟩ := hM (Finsupp.mapDomain some
        (Finsupp.mapDomain (fun x : Ψ × Fin N => (σ x.1, x.2)) (∑ k, Finsupp.single (w k) 1)))
    obtain ⟨L2, h2⟩ := hM' (Finsupp.mapDomain some (∑ k, Finsupp.single (w k) 1))
    rw [h1.limUnder_eq, h2.limUnder_eq]
    rw [hf] at h1
    rw [hg] at h2
    exact sub_eq_zero.1 (tendsto_nhds_unique (h1.sub h2) (hlim w))
  · have h0 : ∀ (K : RootModel Ψ N) (m : Ψ × Fin N →₀ ℕ), m.degree = μ.degree →
        (fun t => K.arMono II t (Finsupp.mapDomain some m)) = fun _ => 0 := by
      intro K m hm
      funext t
      rw [RootModel.arMono, if_neg (by rw [degree_mapDomain, hm]; exact hd)]
    rw [h0 M _ (degree_mapDomain _ μ), h0 M' μ rfl]

/- English proof (translation)
Introduce `Ψ _ _ N T II Γ hC htr hlim hII`. Use `⟨Γ, htr, fun σ hσ B hB F => ?_⟩` and prove the remaining obligations. Take `⟨π, hπ⟩` from `hlim σ hσ B hB`. Establish `hb : ∀ (m : Option (Ψ × Fin N) →₀ ℕ) (a : ℝ), (monomial m a : RPA Ψ N) = a • (basisMonomials (Option (Ψ × Fin N)) ℝ) m`. Introduce `m a`.

Simplify using `[coe_basisMonomials, smul_monomial]`. Establish `hmono : ∀ (c : T.Comp) (μ : Ψ × Fin N →₀ ℕ) (a : ℝ), T.PPc II B c (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) (monomial μ a)) = T.PPc II B (π c) (monomial μ a)`. Introduce `c μ a`. Simplify using `only [RootTower.PPc, toA, rename_monomial]`. Rewrite using `[hb, hb, map_smul, map_smul, RootModel.PP, RootModel.PP, Module.Basis.constr_basis, Module.Basis.constr_basis, limUnder_arMono_perm (T.M B c) (T.M B (π c)) II hII (hC B c) (hC B (π c)) σ (hπ c) μ]`.

Establish `hsum : ∀ (c : T.Comp) (f : RP Ψ N →ₐ[ℝ] RP Ψ N), T.PPc II B c (f F) = ∑ μ ∈ F.support, T.PPc II B c (f (monomial μ (F.coeff μ)))`. Introduce `c f`. Use `conv_lhs => rw [F.as_sum]`. Simplify using `only [RootTower.PPc, toA, map_sum]`. Combine the equalities or inequalities in the displayed calculation.

Unfold `RootTower.PPt`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[hsum c (rename (fun x : Ψ × Fin N => (σ x.1, x.2)))]`. Conclude with `Finset.sum_congr rfl fun μ _ => hmono c μ _`. Use `_ = ∑ c, ∑ μ ∈ F.support, T.PPc II B c (monomial μ (F.coeff μ)) := Equiv.sum_comp π (fun c => ∑ μ ∈ F.support, T.PPc II B c (monomial μ (F.coeff μ)))`.

Use `_ = T.PPt II B F := by`. Unfold `RootTower.PPt`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `hsum c (AlgHom.id ℝ (RP Ψ N))` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem propA_of_limits : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : GlobalTheory.CompanionTheory.Ar.Top.RootTower Ψ N)
    (II : IntersectionSystem) (Γ : Subgroup (Equiv.Perm Ψ)), T.Conv II → (∀ τ τ' : Ψ, ∃ s ∈ Γ, s τ = τ') →
    (∀ s ∈ Γ, ∀ B : ℕ, 2 ≤ B → ∃ π : Equiv.Perm T.Comp, ∀ (c : T.Comp)
      (w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N),
      Tendsto (fun t => II _ _ (T.M B c).P _ (fun j => (T.M B c).x t (s (w j).1, (w j).2)) / (T.M B c).δ -
        II _ _ (T.M B (π c)).P _ (fun j => (T.M B (π c)).x t (w j)) / (T.M B (π c)).δ) (𝓝[>] 0) (𝓝 0)) →
    IsIntersectionSystem II → T.PropA II := by
  intro Ψ _ _ N T II Γ hC htr hlim hII
  refine ⟨Γ, htr, fun σ hσ B hB F => ?_⟩
  obtain ⟨π, hπ⟩ := hlim σ hσ B hB
  have hb : ∀ (m : Option (Ψ × Fin N) →₀ ℕ) (a : ℝ),
      (monomial m a : RPA Ψ N) = a • (basisMonomials (Option (Ψ × Fin N)) ℝ) m := by
    intro m a
    simp [coe_basisMonomials, smul_monomial]
  have hmono : ∀ (c : T.Comp) (μ : Ψ × Fin N →₀ ℕ) (a : ℝ),
      T.PPc II B c (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) (monomial μ a)) =
        T.PPc II B (π c) (monomial μ a) := by
    intro c μ a
    simp only [RootTower.PPc, toA, rename_monomial]
    rw [hb, hb, map_smul, map_smul, RootModel.PP, RootModel.PP, Module.Basis.constr_basis,
      Module.Basis.constr_basis,
      limUnder_arMono_perm (T.M B c) (T.M B (π c)) II hII (hC B c) (hC B (π c)) σ (hπ c) μ]
  have hsum : ∀ (c : T.Comp) (f : RP Ψ N →ₐ[ℝ] RP Ψ N),
      T.PPc II B c (f F) = ∑ μ ∈ F.support, T.PPc II B c (f (monomial μ (F.coeff μ))) := by
    intro c f
    conv_lhs => rw [F.as_sum]
    simp only [RootTower.PPc, toA, map_sum]
  calc T.PPt II B (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F)
      = ∑ c, ∑ μ ∈ F.support, T.PPc II B (π c) (monomial μ (F.coeff μ)) := by
        unfold RootTower.PPt
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hsum c (rename (fun x : Ψ × Fin N => (σ x.1, x.2)))]
        exact Finset.sum_congr rfl fun μ _ => hmono c μ _
    _ = ∑ c, ∑ μ ∈ F.support, T.PPc II B c (monomial μ (F.coeff μ)) :=
        Equiv.sum_comp π (fun c => ∑ μ ∈ F.support, T.PPc II B c (monomial μ (F.coeff μ)))
    _ = T.PPt II B F := by
        unfold RootTower.PPt
        refine Finset.sum_congr rfl fun c _ => ?_
        have := hsum c (AlgHom.id ℝ (RP Ψ N))
        simpa using this.symm

end GlobalTheory.CompanionTheory.Ar.Top.PermInv
