import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelAtPrimeEqSumTorsionTranslates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProductStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

set_option maxHeartbeats 1000000 in
open GlobalTheory.NormSum.KernelAt in
/- English proof (translation)
Introduce `D hI cc hcc δ t0 hC hT a d e0 hvac Ls Lt hLs hLt p _ lam hEs hEt Q hQ`. Substitute `hcc` using the available equality. Establish `hp : p.Prime` using `Fact.out`. Take `⟨s₁, hs₁, -, hs₁a⟩` from `hEs`. Take `⟨s₂, hs₂, hs₂a, -⟩` from `hEt`.

Establish `hLa` using `smul_mem_La ⊤ δ (smul_mem_YYl (smul_mem_homL hs₁a hs₂a))`. Establish `hsp : Nat.Coprime (s₂ * s₁) p` using `Nat.Coprime.mul_left hs₂ hs₁`. Take `⟨-, -, -, -, hfg, -⟩` from `GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 ⊤ δ hC a d _ (Or.inr ⟨Ls, Lt, hLs, hLt, rfl⟩)`. Establish `hi₁` using `coprime_index (La0 D (tor0 D ⊤ δ) a d) _ hfg _ p hp hsp hLa`. Take `⟨b, ε, hb, hloc, hε, hεn, hi₀, he0⟩` from `hvac.2.2.2.2 p lam (by simp)`.

Take `⟨-, -, hB, -⟩` from `GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 ⊤ δ hC a d _ (Or.inl ⟨_, b, hb, rfl⟩)`. Take `⟨n₀, hn₀⟩ : ∃ n₀, n₀ = ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) a d)).index` from `⟨_, rfl⟩`. Establish `hMp : Nat.Coprime (n₀ * (s₂ * s₁)) p` using `Nat.Coprime.mul_left (hn₀ ▸ hi₀) hsp`. Establish `hM0 : n₀ * (s₂ * s₁) ≠ 0`. Introduce `h0`.

Rewrite `hMp` using `[h0, Nat.coprime_zero_left]`. Conclude with `hp.one_lt.ne' hMp`. Establish `hn : n₀ * (s₂ * s₁) * Q ≠ 0` using `mul_ne_zero hM0 hQ.ne'`. Establish `a0 : ∀ x ∈ La0 D (tor0 D ⊤ δ) a d, n₀ • x ∈ LaB D (tor0 D ⊤ δ) b` using `fun x hx => by`. Rewrite using `[hn₀]`.

Conclude with `((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) a d)).nsmul_index_mem ⟨x, hx⟩`. Establish `a1 : ∀ x ∈ La D (tor0 D ⊤ δ) Ls Lt, (n₀ * (s₂ * s₁)) • x ∈ LaB D (tor0 D ⊤ δ) b` using `fun x hx => by`. Rewrite using `[mul_smul]`. Conclude with `a0 _ (hLa x hx)`. Establish `c0 : Cmb D (tor0 D ⊤ δ) lam (LaB D (tor0 D ⊤ δ) b) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0)) (n₀ * (s₂ * s₁) * Q) (1 * 1) e0`.

Rewrite using `[he0]`. Use `Cmb.smul ⟨hε, ?_⟩ (Cmb.iop hn hB hi₀ (fun x hx => ?_) Cmb.base)` and prove the remaining obligations. Rewrite `hεn` using `[lamC, dif_pos hε]`. Conclude with `hεn.le`. Rewrite using `[mul_assoc n₀, mul_comm n₀, mul_smul]`.

Conclude with `AddSubgroup.nsmul_mem _ (a0 x hx) _`. Establish `c1` using `Cmb.iop hn hB hi₁ (fun x hx => by`. Rewrite using `[mul_comm _ Q, mul_smul]`. Conclude with `AddSubgroup.nsmul_mem _ (a1 x hx) _) c0`. Rewrite `c1` using `[one_mul]`.

Use `⟨b, n₀ * (s₂ * s₁), hb, hloc, Nat.pos_of_ne_zero hM0, hMp, fun s hs => ?_⟩` and prove the remaining obligations. Use `Cmb.transl hn hB ?_ c1` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `a1 _ hs`.
-/
theorem UpperTheory.WildA.cmbIop :
    ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)), cc = ⊤ → ∀ (δ t0 : ℂ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 →
      ∀ (a b : ℕ) (e0 : VC D a b → ℂ), oddE0 D cc δ t0 a b e0 →
      ∀ (Ls : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), SD D Ls → SD D Lt →
      ∀ (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), EqAt D l Ls (stdL D a) → EqAt D l Lt (stdL D b) → ∀ k : ℕ, 0 < k →
      ∃ (β : Fin (fF D * a * b) → Matrix (Fin b) (Fin a) D.host.E) (M : ℕ), OnB D β ∧ LocBasis D l (YYl D (stdL D a) (stdL D b)) β ∧
        0 < M ∧ Nat.Coprime M l ∧ ∀ s : VC D a b, k • s ∈ La D (tor0 D cc δ) Ls Lt →
          KernelAt.Cmb D (tor0 D cc δ) lam (LaB D (tor0 D cc δ) β) (pullB D (tor0 D cc δ) β (GL3Theta.th0 (lamOf D cc δ) t0)) (M * k) 1
            (U D (tor0 D cc δ) s (Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a b) (La D (tor0 D cc δ) Ls Lt) e0)) := by
  intro D hI cc hcc δ t0 hC hT a d e0 hvac Ls Lt hLs hLt p _ lam hEs hEt Q hQ
  subst hcc
  have hp : p.Prime := Fact.out
  obtain ⟨s₁, hs₁, -, hs₁a⟩ := hEs
  obtain ⟨s₂, hs₂, hs₂a, -⟩ := hEt
  have hLa := smul_mem_La ⊤ δ (smul_mem_YYl (smul_mem_homL hs₁a hs₂a))
  have hsp : Nat.Coprime (s₂ * s₁) p := Nat.Coprime.mul_left hs₂ hs₁
  obtain ⟨-, -, -, -, hfg, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 ⊤ δ hC a d _
    (Or.inr ⟨Ls, Lt, hLs, hLt, rfl⟩)
  have hi₁ := coprime_index (La0 D (tor0 D ⊤ δ) a d) _ hfg _ p hp hsp hLa
  obtain ⟨b, ε, hb, hloc, hε, hεn, hi₀, he0⟩ := hvac.2.2.2.2 p lam (by simp)
  obtain ⟨-, -, hB, -⟩ := GlobalTheory.T.theta_space_selfDual_pair_at_most_line D hI.g1 ⊤ δ hC a d _ (Or.inl ⟨_, b, hb, rfl⟩)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) a d)).index := ⟨_, rfl⟩
  have hMp : Nat.Coprime (n₀ * (s₂ * s₁)) p := Nat.Coprime.mul_left (hn₀ ▸ hi₀) hsp
  have hM0 : n₀ * (s₂ * s₁) ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hMp
    exact hp.one_lt.ne' hMp
  have hn : n₀ * (s₂ * s₁) * Q ≠ 0 := mul_ne_zero hM0 hQ.ne'
  have a0 : ∀ x ∈ La0 D (tor0 D ⊤ δ) a d, n₀ • x ∈ LaB D (tor0 D ⊤ δ) b := fun x hx => by
    rw [hn₀]
    exact ((LaB D (tor0 D ⊤ δ) b).addSubgroupOf (La0 D (tor0 D ⊤ δ) a d)).nsmul_index_mem ⟨x, hx⟩
  have a1 : ∀ x ∈ La D (tor0 D ⊤ δ) Ls Lt, (n₀ * (s₂ * s₁)) • x ∈ LaB D (tor0 D ⊤ δ) b := fun x hx => by
    rw [mul_smul]
    exact a0 _ (hLa x hx)
  have c0 : Cmb D (tor0 D ⊤ δ) lam (LaB D (tor0 D ⊤ δ) b) (pullB D (tor0 D ⊤ δ) b (GL3Theta.th0 (lamOf D ⊤ δ) t0))
      (n₀ * (s₂ * s₁) * Q) (1 * 1) e0 := by
    rw [he0]
    refine Cmb.smul ⟨hε, ?_⟩ (Cmb.iop hn hB hi₀ (fun x hx => ?_) Cmb.base)
    · rw [lamC, dif_pos hε] at hεn
      exact hεn.le
    · rw [mul_assoc n₀, mul_comm n₀, mul_smul]
      exact AddSubgroup.nsmul_mem _ (a0 x hx) _
  have c1 := Cmb.iop hn hB hi₁ (fun x hx => by
    rw [mul_comm _ Q, mul_smul]
    exact AddSubgroup.nsmul_mem _ (a1 x hx) _) c0
  rw [one_mul] at c1
  refine ⟨b, n₀ * (s₂ * s₁), hb, hloc, Nat.pos_of_ne_zero hM0, hMp, fun s hs => ?_⟩
  refine Cmb.transl hn hB ?_ c1
  rw [mul_smul]
  exact a1 _ hs
