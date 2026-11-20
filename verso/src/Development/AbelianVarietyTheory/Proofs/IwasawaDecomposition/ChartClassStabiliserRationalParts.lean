import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

/- English proof (translation)
Introduce `X n ST SG Q y β _ _ Λ Θ p₀ pref cq hI hD c b hb C hC D hD2 γ`. Establish `img : ∀ (θ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (C : Set (Sp X.E n)), (fun v => θ v) '' C = C ↔ ∀ v, θ v ∈ C ↔ v ∈ C`. Introduce `θ C`. Prove the components needed by the constructor for the conclusion. Introduce `h v`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Rewrite `hv` using `[← h]`. Take `⟨w, hw, e⟩` from `hv`. Rewrite using `[← θ.injective e]` and apply the resulting hypothesis.

Introduce `hv`. Rewrite using `[← h]`. Conclude with `⟨v, hv, rfl⟩`. Introduce `h`. Use extensionality with `v`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `(h w).2 hw`. Introduce `hv`. Use `⟨θ.symm v, (h _).1 ?_, θ.apply_symm_apply v⟩` and prove the remaining obligations.

Rewrite using `[θ.apply_symm_apply]` and apply the resulting hypothesis. Substitute `hb hC hD2` using the available equality. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨g, hg⟩, rfl⟩ replace hg : ya (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c := hg`. Establish `hq : ∀ P, g.2.2.1 P ∈ GlobalTheory.Mem.Col2.ChEx.frStab P.1 (cq (rp Λ Θ p₀ pref c) P)` using `fun P => by`.

Establish `h` using `hI (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) P`. Rewrite `h` using `[hg]`. Conclude with `GlobalTheory.Mem.Col2.ChEx.mem_frStab.2 ((img _ _).1 h.symm)`. Use `⟨(g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, (bar_ya_eq_iff _ _ _ _).1 (congrArg bar hg)⟩⟩, ⟨g.2.2.1, GlobalTheory.Mem.Col2.ChEx.mem_cutQ_grp.2 ⟨g.2.2.2, hq⟩⟩), rfl, ?_⟩` and prove the remaining obligations. Conclude with `congrArg (fun q : PtY ST SG Q y => q.1.1) hg`.

Introduce and unpack `⟨g, rfl, hg⟩`. Establish `hq` using `(GlobalTheory.Mem.Col2.ChEx.mem_cutQ_grp.1 g.2.2.2).2`. Use `⟨⟨(g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, GlobalTheory.Mem.Col2.ChEx.cutQ_grp_le _ _ g.2.2.2⟩), ?_⟩, rfl⟩` and prove the remaining obligations. Use `show ya (Λ c.1) (Θ c.1) _ (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c`. Use `hD _ _ hg ((bar_ya_eq_iff _ _ _ _).2 (mem_chG.1 g.2.1.2).2) ?_` and prove the remaining obligations.

Use function extensionality and compare the values at `P`. Rewrite using `[hI]`. Conclude with `(img _ _).2 (GlobalTheory.Mem.Col2.ChEx.mem_frStab.1 (hq P))`.
-/
theorem GlobalTheory.Mem.Col2.ChEx.stM_range_tw : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (p₀ : DecoF X.E n ST SG Q → Prop) (pref : β → PtY ST SG Q y → Prop) (cq : PtY ST SG Q y → ∀ P : Q, Set (Sp X.E n)), GlobalTheory.Mem.Col2.ChEx.InvActs cq → GlobalTheory.Mem.Col2.ChEx.PtDet cq → ∀ (c : (stR Λ Θ p₀ pref).Cl) (b : β), c.1 = b → ∀ (C : ∀ w : SG, Set (Fin n → 𝓞 X.E ⧸ w.1.asIdeal)), bar (rp Λ Θ p₀ pref c) = C → ∀ (D : ∀ P : Q, Set (Sp X.E n)), cq (rp Λ Θ p₀ pref c) = D → ∀ (γ : GL (Fin n) X.E), (γ ∈ (stM Λ Θ p₀ pref c).range ↔ ∃ g : UF X.E n × ↥(chG (Λ b) C) × ↥(GlobalTheory.Mem.Col2.ChEx.cutQ (Θ b) D).grp, ufGL X.E n g.1 = γ ∧ g • (rp Λ Θ p₀ pref c).1.1 = (rp Λ Θ p₀ pref c).1.1) := by
  intro X n ST SG Q y β _ _ Λ Θ p₀ pref cq hI hD c b hb C hC D hD2 γ
  have img : ∀ (θ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (C : Set (Sp X.E n)), (fun v => θ v) '' C = C ↔ ∀ v, θ v ∈ C ↔ v ∈ C := by
    intro θ C
    constructor
    · intro h v
      constructor
      · intro hv
        rw [← h] at hv
        obtain ⟨w, hw, e⟩ := hv
        rwa [← θ.injective e]
      · intro hv
        rw [← h]
        exact ⟨v, hv, rfl⟩
    · intro h
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (h w).2 hw
      · intro hv
        refine ⟨θ.symm v, (h _).1 ?_, θ.apply_symm_apply v⟩
        rwa [θ.apply_symm_apply]
  subst hb hC hD2
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    replace hg : ya (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c := hg
    have hq : ∀ P, g.2.2.1 P ∈ GlobalTheory.Mem.Col2.ChEx.frStab P.1 (cq (rp Λ Θ p₀ pref c) P) := fun P => by
      have h := hI (Λ c.1) (Θ c.1) g (rp Λ Θ p₀ pref c) P
      rw [hg] at h
      exact GlobalTheory.Mem.Col2.ChEx.mem_frStab.2 ((img _ _).1 h.symm)
    refine ⟨(g.1, ⟨g.2.1.1, mem_chG.2 ⟨g.2.1.2, (bar_ya_eq_iff _ _ _ _).1 (congrArg bar hg)⟩⟩,
      ⟨g.2.2.1, GlobalTheory.Mem.Col2.ChEx.mem_cutQ_grp.2 ⟨g.2.2.2, hq⟩⟩), rfl, ?_⟩
    exact congrArg (fun q : PtY ST SG Q y => q.1.1) hg
  · rintro ⟨g, rfl, hg⟩
    have hq := (GlobalTheory.Mem.Col2.ChEx.mem_cutQ_grp.1 g.2.2.2).2
    refine ⟨⟨(g.1, ⟨g.2.1.1, chG_le _ _ g.2.1.2⟩, ⟨g.2.2.1, GlobalTheory.Mem.Col2.ChEx.cutQ_grp_le _ _ g.2.2.2⟩), ?_⟩, rfl⟩
    show ya (Λ c.1) (Θ c.1) _ (rp Λ Θ p₀ pref c) = rp Λ Θ p₀ pref c
    refine hD _ _ hg ((bar_ya_eq_iff _ _ _ _).2 (mem_chG.1 g.2.1.2).2) ?_
    funext P
    rw [hI]
    exact (img _ _).2 (GlobalTheory.Mem.Col2.ChEx.mem_frStab.1 (hq P))
