import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.DerKer
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.HermitianForms.UnitaryLattices.UnitaryHypotheses.BlkAtApply
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.BZMir GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Form.U.Asm

open PositivityTheory.RgUd.Form

section Abstract

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `w ⟨n, v, rfl⟩`. Conclude with `⟨⟨n, hN n.2⟩, v, by rw [hθ]⟩`.
-/
theorem twKer_mono (ρ : Representation ℂ G V) {N₁ N₂ : Subgroup G} (θ₁ : N₁ →* ℂˣ) (θ₂ : N₂ →* ℂˣ) (hN : N₁ ≤ N₂)
    (hθ : ∀ u : N₁, θ₂ ⟨u, hN u.2⟩ = θ₁ u) : twKer ρ N₁ θ₁ ≤ twKer ρ N₂ θ₂ := by
  apply Submodule.span_mono
  rintro w ⟨n, v, rfl⟩
  exact ⟨⟨n, hN n.2⟩, v, by rw [hθ]⟩

/- English proof (translation)
The claim follows from `Complex.conj_eq_iff_im.mp (hB v v).symm`.
-/
theorem diag_real {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} (hB : ∀ v w, B w v = starRingEnd ℂ (B v w)) (v : V) :
    (B v v).im = 0 := Complex.conj_eq_iff_im.mp (hB v v).symm

end Abstract

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Chars

/- English proof (translation)
Establish `hfix` using `(GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).mp hu`. Unfold `whitCharFrom`. Simplify using `only [MonoidHom.coe_mk, OneHom.coe_mk]`. Use `congr 2`. Use `symm`.

Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `p hp`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢`. Conclude with `⟨hp.1, hab.trans hp.2⟩`. Introduce `p hp hnot`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hp hnot`. Establish `hlt : (p.1 : ℕ) < b` using `hnot hp.1`. Establish `h2 : (p.2 : ℕ) < ℓ` using `by omega`. Establish `hq` using `hfix p.1 p.2 h2`. Rewrite `hq` using `[Matrix.one_apply_ne]`.

Conclude with `hq`. Introduce `h`. Rewrite `hp` using `[h]`. Use linear arithmetic over natural numbers and integers.
-/
theorem whitCharFrom_eq (ψ : AddChar k Circle) {N ℓ a b : ℕ} (u : unipB k (Fin N))
    (hu : (u : GL (Fin N) k) ∈ colFix k N ℓ) (hab : a ≤ b) (hb : b < ℓ) :
    whitCharFrom k ψ N a u = whitCharFrom k ψ N b u := by
  have hfix := (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).mp hu
  unfold whitCharFrom
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  congr 2
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨hp.1, hab.trans hp.2⟩
  · intro p hp hnot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_le] at hp hnot
    have hlt : (p.1 : ℕ) < b := hnot hp.1
    have h2 : (p.2 : ℕ) < ℓ := by omega
    have hq := hfix p.1 p.2 h2
    rw [Matrix.one_apply_ne] at hq
    · exact hq
    · intro h
      rw [h] at hp
      omega

/- English proof (translation)
The claim follows from `inf_le_inf_left _ (GlobalTheory.CompanionTheory.BZMirStep.colFix_anti hab)`.
-/
theorem derUnip_anti {N a b : ℕ} (hab : b ≤ a) : derUnip k N a ≤ derUnip k N b :=
  inf_le_inf_left _ (GlobalTheory.CompanionTheory.BZMirStep.colFix_anti hab)

/- English proof (translation)
Apply `twKer_mono π _ _ (derUnip_anti hab)` to reduce the goal to its premises. Introduce `u`. Establish `hc : (u : GL (Fin N) k) ∈ colFix k N a` using `(Subgroup.mem_inf.mp u.2).2`. Simplify using `only [MonoidHom.comp_apply]`. Break down `le_total x y with h | h` into its components or cases.

Conclude with `(whitCharFrom_eq ψ _ hc h hy).symm`. Conclude with `whitCharFrom_eq ψ _ hc h hx`.
-/
theorem twKer_derUnip_le (ψ : AddChar k Circle) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) {a b x y : ℕ} (hab : b ≤ a) (hx : x < a) (hy : y < a) :
    twKer π (derUnip k N a) ((whitCharFrom k ψ N x).comp (Subgroup.inclusion (derUnip_le_unipB k N a))) ≤
      twKer π (derUnip k N b) ((whitCharFrom k ψ N y).comp (Subgroup.inclusion (derUnip_le_unipB k N b))) := by
  apply twKer_mono π _ _ (derUnip_anti hab)
  intro u
  have hc : (u : GL (Fin N) k) ∈ colFix k N a := (Subgroup.mem_inf.mp u.2).2
  simp only [MonoidHom.comp_apply]
  rcases le_total x y with h | h
  · exact (whitCharFrom_eq ψ _ hc h hy).symm
  · exact whitCharFrom_eq ψ _ hc h hx

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lvlChar_def (ψ : AddChar k Circle) (N n : ℕ) :
    lvlChar k ψ N n = (whitCharFrom k ψ N (n - 1)).comp (Subgroup.inclusion (derUnip_le_unipB k N n)) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem derChar_def (ψ : AddChar k Circle) (N n : ℕ) :
    derChar k ψ N n = (whitCharFrom k ψ N n).comp (Subgroup.inclusion (derUnip_le_unipB k N n)) := rfl

/- English proof (translation)
Rewrite `hg` using `[GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff]`. Use extensionality with `i j`. Conclude with `hg i j j.2`.
-/
theorem colFix_self {N : ℕ} (g : GL (Fin N) k) (hg : g ∈ colFix k N N) : g = 1 := by
  rw [GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff] at hg
  ext i j
  exact hg i j j.2

/- English proof (translation)
Use `eq_bot_iff.2 (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨u, v, rfl⟩`. Establish `h1 : u = 1` using `Subtype.ext (colFix_self _ u.2.2)`. Substitute `h1` using the available equality. Simplify using the standard rewrite rules.
-/
theorem twKer_derUnip_self (ψ : AddChar k Circle) {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (θ : derUnip k N N →* ℂˣ) : twKer π (derUnip k N N) θ = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro _ ⟨u, v, rfl⟩
  have h1 : u = 1 := Subtype.ext (colFix_self _ u.2.2)
  subst h1
  simp

/- English proof (translation)
Introduce `g hg`. Rewrite using `[GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff]`. Rewrite `hg` using `[mem_unipB]`. Introduce `i j hj`. Break down `eq_or_ne i j with rfl | hij` into its components or cases.

Rewrite using `[hg.2, Matrix.one_apply_eq]`. Rewrite using `[hg.1 i j (lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr (by omega)) (Ne.symm hij)), Matrix.one_apply_ne hij]`.
-/
theorem unipB_le_colFix_one (N : ℕ) : unipB k (Fin N) ≤ colFix k N 1 := by
  intro g hg
  rw [GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff]
  rw [mem_unipB] at hg
  intro i j hj
  rcases eq_or_ne i j with rfl | hij
  · rw [hg.2, Matrix.one_apply_eq]
  · rw [hg.1 i j (lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr (by omega)) (Ne.symm hij)), Matrix.one_apply_ne hij]

end Chars

end PositivityTheory.RgUd.Form.U.Asm
