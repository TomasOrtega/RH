import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.EigInert
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.ExtremeU
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.JacquetLemma
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantHeckeOperatorsCommuteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

noncomputable section

open GlobalTheory.PRep Formalism.UG PositivityTheory.SphericalProduct
open scoped Classical

set_option linter.unusedSectionVars false

namespace PositivityTheory.Rg.BcB.F.Eig.InertBorelEigenvalueBounds

/- English proof (translation)
Establish `htop` using `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f (fun i j _ => hc i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))`. Establish `hex : ∃ χ : ι → ℂ, ∃ v ∈ ⨅ i, (f i).maxGenEigenspace (χ i), μ v ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Apply `hμ` to reduce the goal to its premises.

Establish `hle : (⊤ : Submodule ℂ X) ≤ LinearMap.ker μ`. Rewrite using `[← htop]`. Conclude with `iSup_le fun χ v hv => LinearMap.mem_ker.2 (hne χ v hv)`. Use extensionality with `v`. Conclude with `LinearMap.mem_ker.1 (hle Submodule.mem_top)`.

Take `⟨χ, v, hv, hμv⟩` from `hex`. Establish `hχ : χ = ξ`. Use function extensionality and compare the values at `i`. Establish `hvi` using `(Submodule.mem_iInf _).1 hv i`. Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 hvi`.

Establish `hpow : ∀ m : ℕ, ∀ x, μ (((f i - χ i • 1) ^ m) x) = (ξ i - χ i) ^ m * μ x`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ m ih`. Introduce `x`. Rewrite using `[pow_succ, Module.End.mul_apply, ih]`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hμf, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h0` using `hpow k v`. Rewrite `h0` using `[hk, map_zero]`. Establish `: (ξ i - χ i) ^ k = 0`. Break down `mul_eq_zero.1 h0.symm with h | h` into its components or cases. Conclude with `h`.

Conclude with `absurd h hμv`. Conclude with `(sub_eq_zero.1 (eq_zero_of_pow_eq_zero this)).symm`. Introduce `hbot`. Rewrite `hv` using `[hχ, hbot]`. Conclude with `hμv (by rw [(Submodule.mem_bot ℂ).1 hv, map_zero])`.
-/
theorem iInf_maxGenEig_ne_bot {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    {ι : Type} (f : ι → Module.End ℂ X) (hc : ∀ i j, Commute (f i) (f j)) (ξ : ι → ℂ)
    (μ : Module.Dual ℂ X) (hμ : μ ≠ 0) (hμf : ∀ i x, μ (f i x) = ξ i * μ x) :
    ⨅ i, (f i).maxGenEigenspace (ξ i) ≠ ⊥ := by
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute f
    (fun i j _ => hc i j) (fun i => Module.End.iSup_maxGenEigenspace_eq_top (f i))
  have hex : ∃ χ : ι → ℂ, ∃ v ∈ ⨅ i, (f i).maxGenEigenspace (χ i), μ v ≠ 0 := by
    by_contra hne
    push Not at hne
    apply hμ
    have hle : (⊤ : Submodule ℂ X) ≤ LinearMap.ker μ := by
      rw [← htop]
      exact iSup_le fun χ v hv => LinearMap.mem_ker.2 (hne χ v hv)
    ext v
    exact LinearMap.mem_ker.1 (hle Submodule.mem_top)
  obtain ⟨χ, v, hv, hμv⟩ := hex
  have hχ : χ = ξ := by
    funext i
    have hvi := (Submodule.mem_iInf _).1 hv i
    obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hvi
    have hpow : ∀ m : ℕ, ∀ x, μ (((f i - χ i • 1) ^ m) x) = (ξ i - χ i) ^ m * μ x := by
      intro m
      induction m with
      | zero => intro x; simp
      | succ m ih =>
        intro x
        rw [pow_succ, Module.End.mul_apply, ih]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul,
          hμf, smul_eq_mul]
        ring
    have h0 := hpow k v
    rw [hk, map_zero] at h0
    have : (ξ i - χ i) ^ k = 0 := by
      rcases mul_eq_zero.1 h0.symm with h | h
      · exact h
      · exact absurd h hμv
    exact (sub_eq_zero.1 (eq_zero_of_pow_eq_zero this)).symm
  intro hbot
  rw [hχ, hbot] at hv
  exact hμv (by rw [(Submodule.mem_bot ℂ).1 hv, map_zero])

/- English proof (translation)
Use `set W := ⨅ i, (f i).maxGenEigenspace (ξ i) with hWdef`. Set `S : Submodule ℂ X → Prop` to `fun P => P ≠ ⊥ ∧ P ≤ W ∧ ∀ i, ∀ x ∈ P, f i x ∈ P`. Establish `hWinv : ∀ i, ∀ x ∈ W, f i x ∈ W`. Introduce `i x hx`. Rewrite `hx`, the goal using `[hWdef, Submodule.mem_iInf]`.

Introduce `j`. Conclude with `Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) (ξ j) (hx j)`. Establish `hex : ∃ d, ∃ P, S P ∧ Module.finrank ℂ P = d` using `⟨_, W, ⟨hW, le_rfl, hWinv⟩, rfl⟩`. Take `⟨P, hP, hPd⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ Q, S Q → Module.finrank ℂ P ≤ Module.finrank ℂ Q`.

Introduce `Q hQ`. Rewrite using `[hPd]`. Conclude with `Nat.find_min' hex ⟨Q, hQ, rfl⟩`. Establish `hall : ∀ i, ∀ x ∈ P, f i x = ξ i • x`. Introduce `i`.

Use `set N := f i - ξ i • (1 : Module.End ℂ X) with hN`. Set `Q` to `P ⊓ LinearMap.ker N`. Establish `hNP : ∀ z ∈ P, N z ∈ P`. Introduce `z hz`. Simplify using `only [hN, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`.

Conclude with `P.sub_mem (hP.2.2 i z hz) (P.smul_mem _ hz)`. Establish `hQ : S Q`. Use `⟨?_, inf_le_left.trans hP.2.1, ?_⟩` and prove the remaining obligations. Introduce `hQ0`. Take `⟨x, hxP, hx0⟩` from `(Submodule.ne_bot_iff _).1 hP.1`.

Establish `hxW` using `hP.2.1 hxP`. Take `⟨k, hk⟩` from `(Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hxW i)`. Establish `hind : ∀ m : ℕ, (N ^ m) x ∈ P ∧ (N ^ m) x ≠ 0`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simpa using ⟨hxP, hx0⟩`. Consider the case `succ m ih`. Rewrite using `[pow_succ', Module.End.mul_apply]`. Use `⟨hNP _ ih.1, fun h0 => ih.2 ?_⟩` and prove the remaining obligations. Establish `hzQ : (N ^ m) x ∈ Q` using `Submodule.mem_inf.2 ⟨ih.1, LinearMap.mem_ker.2 h0⟩`.

Rewrite `hzQ` using `[hQ0]`. Conclude with `(Submodule.mem_bot ℂ).1 hzQ`. Conclude with `(hind k).2 hk`. Introduce `j x hx`. Take `⟨hxP, hxk⟩` from `Submodule.mem_inf.1 hx`.

Use `Submodule.mem_inf.2 ⟨hP.2.2 j x hxP, ?_⟩` and prove the remaining obligations. Rewrite `hxk`, the goal using `[LinearMap.mem_ker]`. Establish `hcomm : N * f j = f j * N`. Rewrite using `[hN, sub_mul, mul_sub, (hc i j).eq, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`. Rewrite using `[← Module.End.mul_apply, hcomm, Module.End.mul_apply, hxk, map_zero]`.

Establish `heq : Q = P` using `Submodule.eq_of_le_of_finrank_le inf_le_left (hmin Q hQ)`. Introduce `x hx`. Establish `hxQ : x ∈ Q` using `heq ▸ hx`. Establish `h` using `LinearMap.mem_ker.1 (Submodule.mem_inf.1 hxQ).2`. Simplify using `only [hN, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h`.

Conclude with `sub_eq_zero.1 h`. Take `⟨y, hyP, hy0⟩` from `(Submodule.ne_bot_iff _).1 hP.1`. Conclude with `⟨y, hy0, fun i => hall i y hyP⟩`.
-/
theorem exists_common_eigvec {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X]
    {ι : Type} (f : ι → Module.End ℂ X) (hc : ∀ i j, Commute (f i) (f j)) (ξ : ι → ℂ)
    (hW : ⨅ i, (f i).maxGenEigenspace (ξ i) ≠ ⊥) :
    ∃ y : X, y ≠ 0 ∧ ∀ i, f i y = ξ i • y := by
  set W := ⨅ i, (f i).maxGenEigenspace (ξ i) with hWdef
  let S : Submodule ℂ X → Prop := fun P => P ≠ ⊥ ∧ P ≤ W ∧ ∀ i, ∀ x ∈ P, f i x ∈ P
  have hWinv : ∀ i, ∀ x ∈ W, f i x ∈ W := by
    intro i x hx
    rw [hWdef, Submodule.mem_iInf] at hx ⊢
    intro j
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (hc j i) (ξ j) (hx j)
  have hex : ∃ d, ∃ P, S P ∧ Module.finrank ℂ P = d := ⟨_, W, ⟨hW, le_rfl, hWinv⟩, rfl⟩
  obtain ⟨P, hP, hPd⟩ := Nat.find_spec hex
  have hmin : ∀ Q, S Q → Module.finrank ℂ P ≤ Module.finrank ℂ Q := by
    intro Q hQ
    rw [hPd]
    exact Nat.find_min' hex ⟨Q, hQ, rfl⟩
  have hall : ∀ i, ∀ x ∈ P, f i x = ξ i • x := by
    intro i
    set N := f i - ξ i • (1 : Module.End ℂ X) with hN
    let Q := P ⊓ LinearMap.ker N
    have hNP : ∀ z ∈ P, N z ∈ P := by
      intro z hz
      simp only [hN, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact P.sub_mem (hP.2.2 i z hz) (P.smul_mem _ hz)
    have hQ : S Q := by
      refine ⟨?_, inf_le_left.trans hP.2.1, ?_⟩
      · intro hQ0
        obtain ⟨x, hxP, hx0⟩ := (Submodule.ne_bot_iff _).1 hP.1
        have hxW := hP.2.1 hxP
        obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hxW i)
        have hind : ∀ m : ℕ, (N ^ m) x ∈ P ∧ (N ^ m) x ≠ 0 := by
          intro m
          induction m with
          | zero => simpa using ⟨hxP, hx0⟩
          | succ m ih =>
            rw [pow_succ', Module.End.mul_apply]
            refine ⟨hNP _ ih.1, fun h0 => ih.2 ?_⟩
            have hzQ : (N ^ m) x ∈ Q := Submodule.mem_inf.2 ⟨ih.1, LinearMap.mem_ker.2 h0⟩
            rw [hQ0] at hzQ
            exact (Submodule.mem_bot ℂ).1 hzQ
        exact (hind k).2 hk
      · intro j x hx
        obtain ⟨hxP, hxk⟩ := Submodule.mem_inf.1 hx
        refine Submodule.mem_inf.2 ⟨hP.2.2 j x hxP, ?_⟩
        rw [LinearMap.mem_ker] at hxk ⊢
        have hcomm : N * f j = f j * N := by
          rw [hN, sub_mul, mul_sub, (hc i j).eq, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
        rw [← Module.End.mul_apply, hcomm, Module.End.mul_apply, hxk, map_zero]
    have heq : Q = P := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin Q hQ)
    intro x hx
    have hxQ : x ∈ Q := heq ▸ hx
    have h := LinearMap.mem_ker.1 (Submodule.mem_inf.1 hxQ).2
    simp only [hN, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h
    exact sub_eq_zero.1 h
  obtain ⟨y, hyP, hy0⟩ := (Submodule.ne_bot_iff _).1 hP.1
  exact ⟨y, hy0, fun i => hall i y hyP⟩

section Grp

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

/- English proof (translation)
Establish `hd : ∀ c : GL (Fin n) L, IsDiagM c → (c : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (c : Matrix (Fin n) (Fin n) L) i i)`. Introduce `c hc`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ h, hc i j h]`. Use `ext1`. Rewrite using `[Units.val_mul, Units.val_mul, hd a ha, hd b hb, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem diag_comm {a b : GL (Fin n) L} (ha : IsDiagM a) (hb : IsDiagM b) : a * b = b * a := by
  have hd : ∀ c : GL (Fin n) L, IsDiagM c →
      (c : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (c : Matrix (Fin n) (Fin n) L) i i) := by
    intro c hc
    ext i j
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.diagonal_apply_ne _ h, hc i j h]
  ext1
  rw [Units.val_mul, Units.val_mul, hd a ha, hd b hb, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

/- English proof (translation)
Introduce `i j hij` and use `ht i j (ne_of_gt hij)`.
-/
theorem isBorelU_of_diag {t : GU σ n} (ht : IsDiagM (t : GL (Fin n) L)) : IsBorelU t :=
  fun i j hij => ht i j (ne_of_gt hij)

/- English proof (translation)
Introduce `i j hij` and use `hu.1 i j hij`.
-/
theorem isBorelU_of_uni {u : GU σ n} (hu : IsUniM (u : GL (Fin n) L)) : IsBorelU u :=
  fun i j hij => hu.1 i j hij

/- English proof (translation)
Establish `h1 : ordL (1 : L) = 0` using `by simp [ordL]; rfl`. Unfold `chiDeltaU`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Rewrite using `[hu.2 ⟨i.val, h⟩, h1]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem chiDeltaU_uni {m : ℕ} (q : ℕ) (α : Fin m → ℂ) {u : GU σ n} (hu : IsUniM (u : GL (Fin n) L)) :
    chiDeltaU q α u = 1 := by
  have h1 : ordL (1 : L) = 0 := by simp [ordL]; rfl
  unfold chiDeltaU
  refine Finset.prod_eq_one fun i _ => ?_
  split_ifs with h
  · rw [hu.2 ⟨i.val, h⟩, h1]; simp
  · rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem psFunU_apply (q : ℕ) (β : Fin (n / 2) → ℂˣ) (g : GU σ n) (φ : GlobalTheory.LFun.psSpaceU σ q β) (x : GU σ n) :
    ((GlobalTheory.LFun.psFunU σ q β g φ : GlobalTheory.LFun.psSpaceU σ q β) : GU σ n → ℂ) x = (φ : GU σ n → ℂ) (x * g) := rfl

end Grp

section Main

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

/- English proof (translation)
Set `lam : V →ₗ[ℂ] ℂ` to `(LinearMap.proj (R := ℂ) (φ := fun _ : GU σ n => ℂ) 1) ∘ₗ (GlobalTheory.LFun.psSpaceU σ q β).subtype ∘ₗ f`. Establish `hlam : ∀ v, lam v = (f v : GU σ n → ℂ) 1` using `fun v => rfl`. Establish `hρ : ∀ (g : GU σ n) (v : V), lam (ρ g v) = (f v : GU σ n → ℂ) g`. Introduce `g v`. Rewrite using `[hlam, hfe, psFunU_apply, one_mul]`.

Establish `hker : twKer ρ D.N 1 ≤ LinearMap.ker lam`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, v, rfl⟩`. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker]`. Establish `hm : IsUniM ((m : GU σ n) : GL (Fin n) L)` using `(hDN _).1 m.2`.

Establish `e : (f v : GU σ n → ℂ) ((m : GU σ n) * 1) = chiDeltaU q (fun i => (β i : ℂ)) (m : GU σ n) * (f v : GU σ n → ℂ) 1` using `(f v).2 (m : GU σ n) 1 (isBorelU_of_uni hm)`. Rewrite `e` using `[mul_one, chiDeltaU_uni q _ hm, one_mul]`. Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hρ]`. Rewrite using `[hlam, e, sub_self]`. Establish `h2` using `jacquet_hecke (GU σ n) D V ρ hsm t ht U hU x`.

Establish `h3 : D.piN ρ t (D.proj ρ (x : V)) = D.proj ρ (ρ (t : GU σ n) (x : V))` using `rfl`. Rewrite `h2` using `[h3]`. Establish `h5` using `hker ((Submodule.Quotient.eq _).1 h2)`. Rewrite `h5` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Rewrite using `[← hlam, h5, hρ]`.

Establish `e : (f (x : V) : GU σ n → ℂ) ((t : GU σ n) * 1) = chiDeltaU q (fun i => (β i : ℂ)) (t : GU σ n) * (f (x : V) : GU σ n → ℂ) 1` using `(f (x : V)).2 (t : GU σ n) 1 (isBorelU_of_diag ((hDT _).1 t.2))`. Rewrite `e` using `[mul_one]`. Conclude with `e`.
-/
theorem hecke_fun (D : CassData (GU σ n)) (hDN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hDT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L))
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (hsm : IsSmooth ρ)
    (q : ℕ) (β : Fin (n / 2) → ℂˣ) (f : V →ₗ[ℂ] GlobalTheory.LFun.psSpaceU σ q β)
    (hfe : ∀ (g : GU σ n) (v : V), f (ρ g v) = GlobalTheory.LFun.psFunU σ q β g (f v))
    (t : D.T) (ht : D.IsDom t) (U : Module.End ℂ (fixed ρ D.J))
    (hU : PositivityTheory.Lbc.IsHeckeOpG ρ D.J (t : GU σ n) U) (x : fixed ρ D.J) :
    (f ((U x : fixed ρ D.J) : V) : GU σ n → ℂ) 1 =
      chiDeltaU q (fun i => (β i : ℂ)) (t : GU σ n) * (f (x : V) : GU σ n → ℂ) 1 := by
  let lam : V →ₗ[ℂ] ℂ := (LinearMap.proj (R := ℂ) (φ := fun _ : GU σ n => ℂ) 1) ∘ₗ
    (GlobalTheory.LFun.psSpaceU σ q β).subtype ∘ₗ f
  have hlam : ∀ v, lam v = (f v : GU σ n → ℂ) 1 := fun v => rfl
  have hρ : ∀ (g : GU σ n) (v : V), lam (ρ g v) = (f v : GU σ n → ℂ) g := by
    intro g v
    rw [hlam, hfe, psFunU_apply, one_mul]
  have hker : twKer ρ D.N 1 ≤ LinearMap.ker lam := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨m, v, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have hm : IsUniM ((m : GU σ n) : GL (Fin n) L) := (hDN _).1 m.2
    have e : (f v : GU σ n → ℂ) ((m : GU σ n) * 1) =
        chiDeltaU q (fun i => (β i : ℂ)) (m : GU σ n) * (f v : GU σ n → ℂ) 1 :=
      (f v).2 (m : GU σ n) 1 (isBorelU_of_uni hm)
    rw [mul_one, chiDeltaU_uni q _ hm, one_mul] at e
    simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub, hρ]
    rw [hlam, e, sub_self]
  have h2 := jacquet_hecke (GU σ n) D V ρ hsm t ht U hU x
  have h3 : D.piN ρ t (D.proj ρ (x : V)) = D.proj ρ (ρ (t : GU σ n) (x : V)) := rfl
  rw [h3] at h2
  have h5 := hker ((Submodule.Quotient.eq _).1 h2)
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h5
  rw [← hlam, h5, hρ]
  have e : (f (x : V) : GU σ n → ℂ) ((t : GU σ n) * 1) =
      chiDeltaU q (fun i => (β i : ℂ)) (t : GU σ n) * (f (x : V) : GU σ n → ℂ) 1 :=
    (f (x : V)).2 (t : GU σ n) 1 (isBorelU_of_diag ((hDT _).1 t.2))
  rw [mul_one] at e
  exact e

/- English proof (translation)
Take `⟨x, hx, hx0⟩` from `(Submodule.ne_bot_iff _).1 hsph`. Establish `hxK : ∀ k ∈ KU σ n, ρ k x = x` using `GlobalTheory.LGrp.mem_fixed.1 hx`. Use `⟨⟨x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hxK k (hJ hk)⟩, ?_⟩` and prove the remaining obligations. Introduce `h0`. Establish `h0' : (f x : GU σ n → ℂ) 1 = 0` using `h0`.

Apply `hx0` to reduce the goal to its premises. Take `⟨φ0, -, -, huniq⟩` from `Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (β i : ℂ)) (fun i => (β i).ne_zero)`. Establish `hsphU : IsSphericalU q (fun i => (β i : ℂ)) (f x : GU σ n → ℂ)`. Introduce `b g k hb hk`. Establish `e1 : (f x : GU σ n → ℂ) (b * g * k) = (f x : GU σ n → ℂ) (b * g)`.

Rewrite using `[← psFunU_apply q β k (f x) (b * g), ← hfe, hxK k hk]`. Rewrite using `[e1]`. Conclude with `(f x).2 b g hb`. Establish `hz` using `huniq _ hsphU`. Establish `hfx : f x = 0`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hz, h0']`. Use function extensionality and compare the values at `g`. Simplify using the standard rewrite rules. Conclude with `hf (by rw [hfx, map_zero])`.
-/
theorem exists_ne_zero_at_one [CompleteSpace L] {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q)
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V)
    (hsph : fixed ρ (KU σ n) ≠ ⊥) (β : Fin (n / 2) → ℂˣ) (f : V →ₗ[ℂ] GlobalTheory.LFun.psSpaceU σ q β)
    (hf : Function.Injective f) (hfe : ∀ (g : GU σ n) (v : V), f (ρ g v) = GlobalTheory.LFun.psFunU σ q β g (f v))
    (J : Subgroup (GU σ n)) (hJ : J ≤ KU σ n) :
    ∃ x : fixed ρ J, (f (x : V) : GU σ n → ℂ) 1 ≠ 0 := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hsph
  have hxK : ∀ k ∈ KU σ n, ρ k x = x := GlobalTheory.LGrp.mem_fixed.1 hx
  refine ⟨⟨x, GlobalTheory.LGrp.mem_fixed.2 fun k hk => hxK k (hJ hk)⟩, ?_⟩
  intro h0
  have h0' : (f x : GU σ n → ℂ) 1 = 0 := h0
  apply hx0
  obtain ⟨φ0, -, -, huniq⟩ := Formalism.UG.Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (β i : ℂ)) (fun i => (β i).ne_zero)
  have hsphU : IsSphericalU q (fun i => (β i : ℂ)) (f x : GU σ n → ℂ) := by
    intro b g k hb hk
    have e1 : (f x : GU σ n → ℂ) (b * g * k) = (f x : GU σ n → ℂ) (b * g) := by
      rw [← psFunU_apply q β k (f x) (b * g), ← hfe, hxK k hk]
    rw [e1]
    exact (f x).2 b g hb
  have hz := huniq _ hsphU
  have hfx : f x = 0 := by
    apply Subtype.ext
    rw [hz, h0']
    funext g
    simp
  exact hf (by rw [hfx, map_zero])

/- English proof (translation)
Establish `hsm : IsSmooth ρ` using `hA.1`. Establish `: FiniteDimensional ℂ (fixed ρ D.J)` using `hA.2 D.J D.isOpen_J D.isCompact_J`. Set `ι` to `{p : D.T × Module.End ℂ (fixed ρ D.J) // D.IsDom p.1 ∧ PositivityTheory.Lbc.IsHeckeOpG ρ D.J (p.1 : GU σ n) p.2}`. Set `F : ι → Module.End ℂ (fixed ρ D.J)` to `fun i => i.1.2`. Set `ξ : ι → ℂ` to `fun i => chiDeltaU q (fun j => (β j : ℂ)) (i.1.1 : GU σ n)`.

Establish `hcommT : ∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J`. Introduce `a ha b hb`. Establish `e : a * b = b * a` using `Subtype.ext (diag_comm ((hDT a).1 ha) ((hDT b).1 hb))`. Establish `e2 : a * b * a⁻¹ * b⁻¹ = 1` using `by rw [e]; group`. Rewrite using `[e2]`.

Conclude with `D.J.one_mem`. Establish `hc : ∀ i j, Commute (F i) (F j)` using `fun i j => GlobalTheory.T.dominant_hecke_operators_commute (GU σ n) D hcommT V ρ hsm i.1.1 j.1.1 i.2.1 j.2.1 i.1.2 j.1.2 i.2.2 j.2.2`. Set `μ : Module.Dual ℂ (fixed ρ D.J)` to `(LinearMap.proj (R := ℂ) (φ := fun _ : GU σ n => ℂ) 1) ∘ₗ (GlobalTheory.LFun.psSpaceU σ q β).subtype ∘ₗ f ∘ₗ (fixed ρ D.J).subtype`. Establish `hμf : ∀ i x, μ (F i x) = ξ i * μ x` using `fun i x => hecke_fun D hDN hDT ρ hsm q β f hfe i.1.1 i.2.1 i.1.2 i.2.2 x`. Establish `hμ : μ ≠ 0`.

Take `⟨x, hx⟩` from `exists_ne_zero_at_one hU ρ hsph β f hf hfe D.J (by rw [hDJ]; exact GlobalTheory.CompanionTheory.KUFactsU.iwU_le_KU σ n)`. Introduce `h0`. Apply `hx` to reduce the goal to its premises. Conclude with `LinearMap.congr_fun h0 x`. Take `⟨y, hy0, hy⟩` from `exists_common_eigvec F hc ξ (iInf_maxGenEig_ne_bot F hc ξ μ hμ hμf)`.

Use `⟨y, hy0, fun t hd hsd U hUt => ?_⟩` and prove the remaining obligations. Establish `hdom` using `((dom_u L ϖ σ q hU n D hDJ hDN hDNm hDT ⟨t, (hDT t).2 hd⟩).2 hsd).1`. Conclude with `hy ⟨(⟨t, (hDT t).2 hd⟩, U), hdom, hUt⟩`.
-/
theorem main_D [CompleteSpace L] {ϖ : L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (D : CassData (GU σ n))
    (hDJ : D.J = IwU σ n) (hDN : ∀ g : GU σ n, g ∈ D.N ↔ IsUniM (g : GL (Fin n) L))
    (hDNm : ∀ g : GU σ n, g ∈ D.Nm ↔ IsLowUniM (g : GL (Fin n) L))
    (hDT : ∀ g : GU σ n, g ∈ D.T ↔ IsDiagM (g : GL (Fin n) L))
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V) (hA : IsAdmissible ρ)
    (hsph : fixed ρ (KU σ n) ≠ ⊥) (β : Fin (n / 2) → ℂˣ) (f : V →ₗ[ℂ] GlobalTheory.LFun.psSpaceU σ q β)
    (hf : Function.Injective f) (hfe : ∀ (g : GU σ n) (v : V), f (ρ g v) = GlobalTheory.LFun.psFunU σ q β g (f v)) :
    ∃ y : fixed ρ D.J, y ≠ 0 ∧ ∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → IsStrictDom (t : GL (Fin n) L) →
      ∀ U : Module.End ℂ (fixed ρ D.J), PositivityTheory.Lbc.IsHeckeOpG ρ D.J t U →
        U y = chiDeltaU q (fun i => (β i : ℂ)) t • y := by
  have hsm : IsSmooth ρ := hA.1
  have : FiniteDimensional ℂ (fixed ρ D.J) := hA.2 D.J D.isOpen_J D.isCompact_J
  let ι := {p : D.T × Module.End ℂ (fixed ρ D.J) //
    D.IsDom p.1 ∧ PositivityTheory.Lbc.IsHeckeOpG ρ D.J (p.1 : GU σ n) p.2}
  let F : ι → Module.End ℂ (fixed ρ D.J) := fun i => i.1.2
  let ξ : ι → ℂ := fun i => chiDeltaU q (fun j => (β j : ℂ)) (i.1.1 : GU σ n)
  have hcommT : ∀ a ∈ D.T, ∀ b ∈ D.T, a * b * a⁻¹ * b⁻¹ ∈ D.J := by
    intro a ha b hb
    have e : a * b = b * a := Subtype.ext (diag_comm ((hDT a).1 ha) ((hDT b).1 hb))
    have e2 : a * b * a⁻¹ * b⁻¹ = 1 := by rw [e]; group
    rw [e2]
    exact D.J.one_mem
  have hc : ∀ i j, Commute (F i) (F j) := fun i j =>
    GlobalTheory.T.dominant_hecke_operators_commute (GU σ n) D hcommT V ρ hsm i.1.1 j.1.1 i.2.1 j.2.1 i.1.2 j.1.2 i.2.2 j.2.2
  let μ : Module.Dual ℂ (fixed ρ D.J) := (LinearMap.proj (R := ℂ) (φ := fun _ : GU σ n => ℂ) 1) ∘ₗ
    (GlobalTheory.LFun.psSpaceU σ q β).subtype ∘ₗ f ∘ₗ (fixed ρ D.J).subtype
  have hμf : ∀ i x, μ (F i x) = ξ i * μ x := fun i x =>
    hecke_fun D hDN hDT ρ hsm q β f hfe i.1.1 i.2.1 i.1.2 i.2.2 x
  have hμ : μ ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne_zero_at_one hU ρ hsph β f hf hfe D.J
      (by rw [hDJ]; exact GlobalTheory.CompanionTheory.KUFactsU.iwU_le_KU σ n)
    intro h0
    apply hx
    exact LinearMap.congr_fun h0 x
  obtain ⟨y, hy0, hy⟩ := exists_common_eigvec F hc ξ (iInf_maxGenEig_ne_bot F hc ξ μ hμ hμf)
  refine ⟨y, hy0, fun t hd hsd U hUt => ?_⟩
  have hdom := ((dom_u L ϖ σ q hU n D hDJ hDN hDNm hDT ⟨t, (hDT t).2 hd⟩).2 hsd).1
  exact hy ⟨(⟨t, (hDT t).2 hd⟩, U), hdom, hUt⟩

end Main

end PositivityTheory.Rg.BcB.F.Eig.InertBorelEigenvalueBounds

namespace PositivityTheory.Rg.BcB.F.Eig

/- English proof (translation)
Introduce `L _ _ _ ϖ σ q n V _ _ ρ α hU hA hI hS`. Take `⟨β, hW, hmono, hge, f, hf, hfe⟩` from `extremeU L ϖ σ q n V ρ α hU hA hI hS`. Use `⟨β, hW, hmono, hge, ?_⟩` and prove the remaining obligations. Take `⟨D, hDJ, hDN, hDNm, hDT⟩` from `iwahori_u L ϖ σ q hU n`. Rewrite using `[← hDJ]`.

Conclude with `InertBorelEigenvalueBounds.main_D hU D hDJ hDN hDNm hDT ρ hA hS.1 β f hf hfe`.
-/
theorem absEig : AbsEig := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hU hA hI hS
  obtain ⟨β, hW, hmono, hge, f, hf, hfe⟩ := extremeU L ϖ σ q n V ρ α hU hA hI hS
  refine ⟨β, hW, hmono, hge, ?_⟩
  obtain ⟨D, hDJ, hDN, hDNm, hDT⟩ := iwahori_u L ϖ σ q hU n
  rw [← hDJ]
  exact InertBorelEigenvalueBounds.main_D hU D hDJ hDN hDNm hDT ρ hA hS.1 β f hf hfe

end PositivityTheory.Rg.BcB.F.Eig

end
