import Formalism.LocalToGlobal.GlobalTheory.GL6.AdelicFunctionRightTranslateDiamond
import Formalism.LocalToGlobal.HermitianForms.FramesLemmas
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL6.FrobeniusIdentitiesNoKernelOfClauses

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG Formalism.L2.DIV
open Formalism.GradedWeylDivisibility (blockAct)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {ι : Type} [Fintype ι]

/- English proof (translation)
Establish `h : cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * J * (γ : Matrix (Fin n) (Fin n) E) = J` using `hγ`. Establish `e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ = (cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (emb τ)`. Use extensionality with `a b`. Simplify using `[atInf, cT, conjTranspose_apply, hc]`. Rewrite using `[e]`.

Simplify using `only [gramC, atInf]`. Rewrite using `[← Matrix.map_mul, ← Matrix.map_mul, h]`.
-/
theorem at_infinity_unitary (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (τ : ι) :
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ =
      gramC J emb τ := by
  have h : cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E) * J * (γ : Matrix (Fin n) (Fin n) E) = J := hγ
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ =
      (cT (σ : E →+* E) (γ : Matrix (Fin n) (Fin n) E)).map (emb τ) := by
    ext a b
    simp [atInf, cT, conjTranspose_apply, hc]
  rw [e]
  simp only [gramC, atInf]
  rw [← Matrix.map_mul, ← Matrix.map_mul, h]

def frameTranslate (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) : Frames (gramC J emb) :=
  ⟨fun τ => atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ, fun τ => by
    rw [det_mul]; exact (isUnit_det_atInf emb γ τ).mul (y.2 τ)⟩

/- English proof (translation)
Introduce `τ` and use `by have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ * (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = (y.1 τ)ᴴ * ((atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ * atInf emb (γ : Matrix (Fin n) (Fin n) E) τ) * y.1 τ := by rw [con …`.
-/
theorem frame_translate_is_orthonormal (emb : ι → E →+* ℂ) (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (y : Frames (gramC J emb)) (hy : y.IsON) :
    (frameTranslate emb hc γ hγ y).IsON := fun τ => by
  have e : (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) =
      (y.1 τ)ᴴ * ((atInf emb (γ : Matrix (Fin n) (Fin n) E) τ)ᴴ * gramC J emb τ *
        atInf emb (γ : Matrix (Fin n) (Fin n) E) τ) * y.1 τ := by
    rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
  show (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = 1 ∨
    (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ)ᴴ * gramC J emb τ *
      (atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * y.1 τ) = -1
  rw [e, at_infinity_unitary emb hc γ hγ τ]
  exact hy τ

/- English proof (translation)
Simplify using `only [atInf]`. Rewrite using `[← Matrix.map_mul, Units.mul_inv]`. Simplify using the standard rewrite rules.
-/
theorem at_infinity_mul_inv (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ = 1 := by
  simp only [atInf]
  rw [← Matrix.map_mul, Units.mul_inv]
  simp

/- English proof (translation)
Apply `hg γ hγ x x' κ hx` to reduce the goal to its premises. Introduce `τ`. Use `show y.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ * (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)`. Rewrite using `[← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]`.
-/
theorem adelic_value_translate (S : StepLevel F E σ J T f bad) (emb : ι → E →+* ℂ)
    (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x))
    {g : UPts σ J (FiniteAdeleRing (𝓞 F) F) → Frames (gramC J emb) → ℂ} (hg : g ∈ AdFun S emb)
    (γ : GL (Fin n) E) (hγ : γ ∈ UJ (σ : E →+* E) J) (x x' : UPts σ J (FiniteAdeleRing (𝓞 F) F)) (κ : S.U)
    (hx : x'.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * x.1 * κ.1) (y : Frames (gramC J emb)) :
    g x' y = (S.chi κ : ℂ) * g x (frameTranslate emb hc γ⁻¹ ((UJ (σ : E →+* E) J).inv_mem hγ) y) := by
  apply hg γ hγ x x' κ hx
  intro τ
  show y.1 τ = atInf emb (γ : Matrix (Fin n) (Fin n) E) τ *
    (atInf emb ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) τ * y.1 τ)
  rw [← Matrix.mul_assoc, at_infinity_mul_inv, Matrix.one_mul]

/- English proof (translation)
Establish `h1 : CSpan lam ≤ VV ℂ lam`. Use `(Formalism.L2.Col.CSpan_le_span (RingHom.id ℂ) lam).trans ?_` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨F', hF', rfl⟩`. Simplify `hF'` using `[MvPolynomial.map_id]`.

Establish `h2 : blockAct ℂ w P ∈ VV ℂ lam` using `(Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n w).2 (fun τ => nablaSq ℂ n (lam τ)) (fun τ => nablaSq ℂ n (lam τ)) (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ f hf) P (h1 hP)`. Simplify `Formalism.L2.Col.map_mem_CSpan (RingHom.id ℂ) lam _ h2` using `[MvPolynomial.map_id]`.
-/
theorem complex_span_block_action_stable (lam : ι → DomWeight n) (w : ι → Matrix (Fin n) (Fin n) ℂ)
    {P : MvPolynomial (ι × Fin n × Fin n) ℂ} (hP : P ∈ CSpan lam) : blockAct ℂ w P ∈ CSpan lam := by
  have h1 : CSpan lam ≤ VV ℂ lam := by
    refine (Formalism.L2.Col.CSpan_le_span (RingHom.id ℂ) lam).trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨F', hF', rfl⟩
    simpa [MvPolynomial.map_id] using hF'
  have h2 : blockAct ℂ w P ∈ VV ℂ lam :=
    (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n w).2 (fun τ => nablaSq ℂ n (lam τ)) (fun τ => nablaSq ℂ n (lam τ))
      (fun τ f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ _ f hf) P (h1 hP)
  simpa [MvPolynomial.map_id] using Formalism.L2.Col.map_mem_CSpan (RingHom.id ℂ) lam _ h2

end Gen

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Rewrite using `[LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sesquilinear_smul_smul {M : Type} [AddCommGroup M] [Module ℂ M] (B : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ) (a : ℂ) (x y : M) :
    B (a • x) (a • y) = (starRingEnd ℂ a * a) * B x y := by
  rw [LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]; ring

/- English proof (translation)
The claim follows from `D.sp.cm.cmUnram.2.1 (embT D τ) x`.
-/
theorem embedding_conj_compat (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (sigD D x) = starRingEnd ℂ (embT D τ x) :=
  D.sp.cm.cmUnram.2.1 (embT D τ) x

/- English proof (translation)
Take `⟨g, hg, hgφ⟩` from `((Tf.val i hi).Fi φ).1 hφ`. Use `⟨g, hg, fun c => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`. Use `congrFun (congrFun hgφ c) ((Tf.val i hi).eY z)` as an intermediate fact. Simplify using `only [Equiv.symm_apply_apply] at this`.

Conclude with `this.symm`.
-/
theorem forms_from_adelic_function (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)
    (hφ : φ ∈ (D.fm u).Fi i) :
    ∃ g ∈ AdForms (Tf.cls i hi).lev (embT D) (lamT u i),
      ∀ c, φ c = fun z => g ((Tf.cls i hi).y c) ((Tf.val i hi).eY z) := by
  obtain ⟨g, hg, hgφ⟩ := ((Tf.val i hi).Fi φ).1 hφ
  refine ⟨g, hg, fun c => ?_⟩
  funext z
  have := congrFun (congrFun hgφ c) ((Tf.val i hi).eY z)
  simp only [Equiv.symm_apply_apply] at this
  exact this.symm

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hv : ∀ {k : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Frames (gramC (gramN D i hi) (embT D)) → ℂ}, k ∈ AdForms (Tf.cls i hi).lev (embT D) (lamT u i) → ∀ x0, ∃ P ∈ CSpan (lamT u i), fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) 1 P = k x0`. Introduce `k hk x0`. Use `(Submodule.mem_pi.1 (Submodule.mem_inf.1 hk).2) x0 (Set.mem_univ _)` as an intermediate fact. Conclude with `Submodule.mem_map.1 this`. Take `⟨P, hP, hPe⟩` from `hv hg x`.

Take `⟨Q, hQ, hQe⟩` from `hv hh x`. Break down `isEmpty_or_nonempty ((D.mem u).C.Y i) with hE | hne` into its components or cases. Establish `e : ∀ k : (D.mem u).C.Y i → ℂ, k = 0` using `fun k => funext fun z => isEmptyElim z`. Rewrite using `[e (fun z => g x' _), e (fun z => h x' _), e (fun z => g x _), e (fun z => h x _)]`. Simplify using the standard rewrite rules.

Take `⟨z0⟩` from `hne`. Take `⟨o, ho⟩` from `(Tf.val i hi).exists_isON (embedding_conj_compat D)`. Establish `hcs : CSpan (lamT u i) = CSpan ((D.fm u).lam i)` using `CSpan_shW _ _`. Establish `hone : (fun τ => o.1 τ * (o.1 τ)⁻¹) = (1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ)`. Use function extensionality and compare the values at `τ`.

Conclude with `Matrix.mul_nonsing_inv _ (Formalism.L2.Col.isUnit_det_fr o τ)`. Take `⟨P0, hP0d⟩ : ∃ P0, P0 = (∏ τ, (o.1 τ).det ^ shiftOf (lamT u i) τ) • blockAct ℂ (fun τ => o.1 τ) P` from `⟨_, rfl⟩`. Take `⟨Q0, hQ0d⟩ : ∃ Q0, Q0 = (∏ τ, (o.1 τ).det ^ shiftOf (lamT u i) τ) • blockAct ℂ (fun τ => o.1 τ) Q` from `⟨_, rfl⟩`. Establish `hP0 : P0 ∈ CSpan ((D.fm u).lam i)`. Rewrite using `[← hcs, hP0d]`.

Conclude with `Submodule.smul_mem _ _ (complex_span_block_action_stable _ _ hP)`. Establish `hQ0 : Q0 ∈ CSpan ((D.fm u).lam i)`. Rewrite using `[← hcs, hQ0d]`. Conclude with `Submodule.smul_mem _ _ (complex_span_block_action_stable _ _ hQ)`. Establish `eP : g x = fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) P0`.

Rewrite using `[← hPe, hP0d, ← hone]`. Conclude with `Formalism.L2.Col.fnOf_mul _ _ (fun τ => o.1 τ) (fun τ => (o.1 τ)⁻¹) P`. Establish `eQ : h x = fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) Q0`. Rewrite using `[← hQe, hQ0d, ← hone]`. Conclude with `Formalism.L2.Col.fnOf_mul _ _ (fun τ => o.1 τ) (fun τ => (o.1 τ)⁻¹) Q`.

Establish `hinv : ∀ τ, (o.1 τ)⁻¹ * atInf (embT D) ((γ⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ = ((frameTranslate (embT D) (embedding_conj_compat D) γ hγ o).1 τ)⁻¹`. Introduce `τ`. Use `show _ = (atInf (embT D) (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ * o.1 τ)⁻¹`. Rewrite using `[Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (at_infinity_mul_inv _ γ τ)]`. Establish `key : ∀ (k : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Frames (gramC (gramN D i hi) (embT D)) → ℂ) (R : MvPolynomial _ ℂ), k ∈ AdForms (Tf.cls i hi).lev (embT D) (lamT u i) → k x = fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o …`.

Introduce `k R hk hkR`. Use function extensionality and compare the values at `z`. Rewrite using `[Pi.smul_apply, smul_eq_mul, adelic_value_translate _ (embT D) (embedding_conj_compat D) (Submodule.mem_inf.1 hk).1 γ hγ x x' κ hx, hkR, Formalism.L2.Col.fnOf_tr (shiftOf (lamT u i)) _ _ R _ _ (fun τ => rfl)]`. Simplify using `only [hinv]`. Rewrite using `[key g P0 hg eP, key h Q0 hh eQ, sesquilinear_smul_smul, (Tf.val i hi).ipV c _ (frame_translate_is_orthonormal _ _ γ hγ o ho) P0 hP0 Q0 hQ0]`.

Establish `e2 : (fun z => g x ((Tf.val i hi).eY z)) = fun z => fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) P0 ((Tf.val i hi).eY z)`. Rewrite using `[eP]`. Establish `e3 : (fun z => h x ((Tf.val i hi).eY z)) = fun z => fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) Q0 ((Tf.val i hi).eY z)`. Rewrite using `[eQ]`. Rewrite using `[e2, e3, (Tf.val i hi).ipV c' o ho P0 hP0 Q0 hQ0, Complex.conj_mul', (Tf.glev i hi).chi_unit κ]`.

Simplify using the standard rewrite rules.
-/
theorem inner_product_translate_eq (Tf : FormsTied D u) (i : ℕ) (hi : i ≤ D.R.m) (c c' : (D.mem u).C.cls i)
    (γ : GL (Fin (D.R.N i)) D.host.E) (hγ : γ ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
    (x x' : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : (Tf.cls i hi).lev.U)
    (hx : x'.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ * x.1 * κ.1)
    {g h : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      Frames (gramC (gramN D i hi) (embT D)) → ℂ}
    (hg : g ∈ AdForms (Tf.cls i hi).lev (embT D) (lamT u i)) (hh : h ∈ AdForms (Tf.cls i hi).lev (embT D) (lamT u i)) :
    (D.fm u).ipV i c (fun z => g x' ((Tf.val i hi).eY z)) (fun z => h x' ((Tf.val i hi).eY z)) =
      (D.fm u).ipV i c' (fun z => g x ((Tf.val i hi).eY z)) (fun z => h x ((Tf.val i hi).eY z)) := by
  have hv : ∀ {k : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      Frames (gramC (gramN D i hi) (embT D)) → ℂ}, k ∈ AdForms (Tf.cls i hi).lev (embT D) (lamT u i) →
      ∀ x0, ∃ P ∈ CSpan (lamT u i), fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) 1 P = k x0 := by
    intro k hk x0
    have := (Submodule.mem_pi.1 (Submodule.mem_inf.1 hk).2) x0 (Set.mem_univ _)
    exact Submodule.mem_map.1 this
  obtain ⟨P, hP, hPe⟩ := hv hg x
  obtain ⟨Q, hQ, hQe⟩ := hv hh x
  rcases isEmpty_or_nonempty ((D.mem u).C.Y i) with hE | hne
  · have e : ∀ k : (D.mem u).C.Y i → ℂ, k = 0 := fun k => funext fun z => isEmptyElim z
    rw [e (fun z => g x' _), e (fun z => h x' _), e (fun z => g x _), e (fun z => h x _)]
    simp
  obtain ⟨z0⟩ := hne
  obtain ⟨o, ho⟩ := (Tf.val i hi).exists_isON (embedding_conj_compat D)
  have hcs : CSpan (lamT u i) = CSpan ((D.fm u).lam i) := CSpan_shW _ _
  have hone : (fun τ => o.1 τ * (o.1 τ)⁻¹) = (1 : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ) := by
    funext τ; exact Matrix.mul_nonsing_inv _ (Formalism.L2.Col.isUnit_det_fr o τ)
  obtain ⟨P0, hP0d⟩ : ∃ P0, P0 = (∏ τ, (o.1 τ).det ^ shiftOf (lamT u i) τ) • blockAct ℂ (fun τ => o.1 τ) P := ⟨_, rfl⟩
  obtain ⟨Q0, hQ0d⟩ : ∃ Q0, Q0 = (∏ τ, (o.1 τ).det ^ shiftOf (lamT u i) τ) • blockAct ℂ (fun τ => o.1 τ) Q := ⟨_, rfl⟩
  have hP0 : P0 ∈ CSpan ((D.fm u).lam i) := by
    rw [← hcs, hP0d]; exact Submodule.smul_mem _ _ (complex_span_block_action_stable _ _ hP)
  have hQ0 : Q0 ∈ CSpan ((D.fm u).lam i) := by
    rw [← hcs, hQ0d]; exact Submodule.smul_mem _ _ (complex_span_block_action_stable _ _ hQ)
  have eP : g x = fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) P0 := by
    rw [← hPe, hP0d, ← hone]
    exact Formalism.L2.Col.fnOf_mul _ _ (fun τ => o.1 τ) (fun τ => (o.1 τ)⁻¹) P
  have eQ : h x = fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) Q0 := by
    rw [← hQe, hQ0d, ← hone]
    exact Formalism.L2.Col.fnOf_mul _ _ (fun τ => o.1 τ) (fun τ => (o.1 τ)⁻¹) Q
  have hinv : ∀ τ, (o.1 τ)⁻¹ * atInf (embT D) ((γ⁻¹ : GL (Fin (D.R.N i)) D.host.E) :
      Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ =
      ((frameTranslate (embT D) (embedding_conj_compat D) γ hγ o).1 τ)⁻¹ := by
    intro τ
    show _ = (atInf (embT D) (γ : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E) τ * o.1 τ)⁻¹
    rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv (at_infinity_mul_inv _ γ τ)]
  have key : ∀ (k : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) →
      Frames (gramC (gramN D i hi) (embT D)) → ℂ) (R : MvPolynomial _ ℂ),
      k ∈ AdForms (Tf.cls i hi).lev (embT D) (lamT u i) →
      k x = fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) R →
      (fun z => k x' ((Tf.val i hi).eY z)) = ((Tf.cls i hi).lev.chi κ : ℂ) • fun z =>
        fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i))
          (fun τ => ((frameTranslate (embT D) (embedding_conj_compat D) γ hγ o).1 τ)⁻¹) R ((Tf.val i hi).eY z) := by
    intro k R hk hkR
    funext z
    rw [Pi.smul_apply, smul_eq_mul,
      adelic_value_translate _ (embT D) (embedding_conj_compat D) (Submodule.mem_inf.1 hk).1 γ hγ x x' κ hx, hkR,
      Formalism.L2.Col.fnOf_tr (shiftOf (lamT u i)) _ _ R _ _ (fun τ => rfl)]
    simp only [hinv]
  rw [key g P0 hg eP, key h Q0 hh eQ, sesquilinear_smul_smul, (Tf.val i hi).ipV c _ (frame_translate_is_orthonormal _ _ γ hγ o ho) P0 hP0 Q0 hQ0]
  have e2 : (fun z => g x ((Tf.val i hi).eY z)) = fun z =>
      fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) P0 ((Tf.val i hi).eY z) := by
    rw [eP]
  have e3 : (fun z => h x ((Tf.val i hi).eY z)) = fun z =>
      fnOf (gramC (gramN D i hi) (embT D)) (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) Q0 ((Tf.val i hi).eY z) := by
    rw [eQ]
  rw [e2, e3, (Tf.val i hi).ipV c' o ho P0 hP0 Q0 hQ0, Complex.conj_mul', (Tf.glev i hi).chi_unit κ]
  simp

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `i hi v c φ hφ ψ hψ`. Take `⟨g, hg, hval⟩` from `forms_from_adelic_function Tf i hi φ hφ`. Take `⟨h, hh, hvalψ⟩` from `forms_from_adelic_function Tf i hi ψ hψ`. Establish `hgA` using `(Submodule.mem_inf.1 hg).1`. Establish `hhA` using `(Submodule.mem_inf.1 hh).1`.

Use `⟨fun x hx1 => ?_, fun gg hgg => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨z, rfl⟩` from `(Tf.lv i hi).pr_surj v c x`. Take `⟨γ, η, κ, -, hmul, -, -, -, hT⟩` from `Tf.up i hi v c z hx1`. Rewrite using `[hval, hvalψ, hT g hgA, hT h hhA]`. Conclude with `inner_product_translate_eq Tf i hi c _ γ.1 γ.2 _ _ κ⁻¹ (by rw [Subgroup.coe_mul, InvMemClass.coe_inv, hmul, mul_inv_cancel_right]) hg hh`.

Take `⟨γ, η, κ, -, hmul, -, -, hT⟩` from `Tf.dn i hi v c gg hgg`. Rewrite using `[hval, hvalψ, hT g hgA, hT h hhA]`. Conclude with `inner_product_translate_eq Tf i hi c _ γ.1 γ.2 _ _ κ⁻¹ (by rw [Subgroup.coe_mul, InvMemClass.coe_inv, hmul, mul_inv_cancel_right]) hg hh`. Take `⟨k, hk, δ, hδ⟩` from `hE i hi v a`. Establish `hq` using `(Tf.val i hi).dil v a k hk c δ hδ`.

Take `⟨hh', hhm, kk, hkm, heq⟩` from `(DoubleCoset.eq _ _ _ _).1 hq`. Take `⟨γ, hγ, hγe⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhm)`. Establish `hkU : kk.1 ∈ (Tf.cls i hi).lev.U` using `Subgroup.mem_subgroupOf.1 hkm`. Rewrite using `[hval, hvalψ, (Tf.val i hi).dilT v a k hk c δ hδ g hgA, (Tf.val i hi).dilT v a k hk c δ hδ h hhA]`. Conclude with `inner_product_translate_eq Tf i hi c _ γ hγ _ _ ⟨kk.1, hkU⟩ (by rw [heq, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]) hg hh`.
-/
theorem transport_iso_of_diamond_elements (Tf : FormsTied D u) (hE : DiamondElementsExist Tf) : Formalism.MainNotions.product_first_zeroth_parts.TrIso D u := by
  intro i hi v c φ hφ ψ hψ
  obtain ⟨g, hg, hval⟩ := forms_from_adelic_function Tf i hi φ hφ
  obtain ⟨h, hh, hvalψ⟩ := forms_from_adelic_function Tf i hi ψ hψ
  have hgA := (Submodule.mem_inf.1 hg).1
  have hhA := (Submodule.mem_inf.1 hh).1
  refine ⟨fun x hx1 => ?_, fun gg hgg => ?_, fun a => ?_⟩
  · obtain ⟨z, rfl⟩ := (Tf.lv i hi).pr_surj v c x
    obtain ⟨γ, η, κ, -, hmul, -, -, -, hT⟩ := Tf.up i hi v c z hx1
    rw [hval, hvalψ, hT g hgA, hT h hhA]
    exact inner_product_translate_eq Tf i hi c _ γ.1 γ.2 _ _ κ⁻¹
      (by rw [Subgroup.coe_mul, InvMemClass.coe_inv, hmul, mul_inv_cancel_right]) hg hh
  · obtain ⟨γ, η, κ, -, hmul, -, -, hT⟩ := Tf.dn i hi v c gg hgg
    rw [hval, hvalψ, hT g hgA, hT h hhA]
    exact inner_product_translate_eq Tf i hi c _ γ.1 γ.2 _ _ κ⁻¹
      (by rw [Subgroup.coe_mul, InvMemClass.coe_inv, hmul, mul_inv_cancel_right]) hg hh
  · obtain ⟨k, hk, δ, hδ⟩ := hE i hi v a
    have hq := (Tf.val i hi).dil v a k hk c δ hδ
    obtain ⟨hh', hhm, kk, hkm, heq⟩ := (DoubleCoset.eq _ _ _ _).1 hq
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhm)
    have hkU : kk.1 ∈ (Tf.cls i hi).lev.U := Subgroup.mem_subgroupOf.1 hkm
    rw [hval, hvalψ, (Tf.val i hi).dilT v a k hk c δ hδ g hgA, (Tf.val i hi).dilT v a k hk c δ hδ h hhA]
    exact inner_product_translate_eq Tf i hi c _ γ hγ _ _ ⟨kk.1, hkU⟩
      (by rw [heq, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]) hg hh

/- English proof (translation)
Introduce `D u hF`. Take `⟨Tf, hc⟩` from `hF`. Conclude with `⟨(hR D u ⟨Tf, hc⟩).1, (hR D u ⟨Tf, hc⟩).2, transport_iso_of_diamond_elements Tf (hD D u Tf hc), diamond_mul_of_diamond_elements Tf (hD D u Tf hc)⟩`.
-/
theorem admissible_of_diamonds_and_round_trips
    (hD : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → DiamondElementsExist Tf)
    (hR : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → Formalism.MainNotions.product_first_zeroth_parts.RoundUp D u ∧ Formalism.MainNotions.product_first_zeroth_parts.RoundDn D u) :
    LinkAdmT := by
  intro D u hF
  obtain ⟨Tf, hc⟩ := hF
  exact ⟨(hR D u ⟨Tf, hc⟩).1, (hR D u ⟨Tf, hc⟩).2, transport_iso_of_diamond_elements Tf (hD D u Tf hc), diamond_mul_of_diamond_elements Tf (hD D u Tf hc)⟩

/- English proof (translation)
Introduce `D u hF hS`. Take `⟨Tf, hc⟩` from `hF`. Take `⟨h7a, h7c, h7d⟩` from `h D u ⟨Tf, hc⟩ hS`. Conclude with `frobenius_identities_no_kernel_of_clauses D u h7a h7c h7d (diamond_mul_of_diamond_elements Tf (hD D u Tf hc))`.
-/
theorem frobenius_no_kernel_of_frobenius_similitude
    (hD : ∀ (D : D7) (u : D.what₂.Word) (Tf : FormsTied D u), ChiFin Tf → DiamondElementsExist Tf)
    (h : ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u →
      (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
        Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ = Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v (Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v φ)) ∧
      (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
        Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i) ∧
      (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i, ∀ ψ ∈ Formalism.MainNotions.product_first_zeroth_parts.MramI D u i,
        (D.fm u).ipC i (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v φ) (Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v ψ) =
          ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ)) :
    FrobeniusNoKernelFamily := by
  intro D u hF hS
  obtain ⟨Tf, hc⟩ := hF
  obtain ⟨h7a, h7c, h7d⟩ := h D u ⟨Tf, hc⟩ hS
  exact frobenius_identities_no_kernel_of_clauses D u h7a h7c h7d (diamond_mul_of_diamond_elements Tf (hD D u Tf hc))

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
