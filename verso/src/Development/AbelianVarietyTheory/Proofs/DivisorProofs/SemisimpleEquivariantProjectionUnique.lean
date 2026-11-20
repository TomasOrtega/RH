import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso

/- English proof (translation)
Introduce `G _ K V _ _ ρ D h1 hmul hst hss P hPP hPc m b A hbD hli hAct hU`. Use `haveI := hss`. Use `set e := (repD ρ D K h1 hmul hst).asModuleEquiv with he`. Use `set Sb : Submodule ℂ V := Submodule.span ℂ (Set.range b) with hSb`. Establish `hSbD : Sb ≤ D` using `Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbD i)`.

Establish `hstab : ∀ k ∈ K, ∀ x ∈ Sb, ρ k x ∈ Sb`. Introduce `k hk x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`.

Rewrite using `[hAct k hk j]`. Conclude with `Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Set `W : Submodule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule` to `{ carrier := {u | ((e u : D) : V) ∈ Sb} add_mem' := by`. Introduce `u v hu hv`. Simplify using `only [Set.mem_setOf_eq, map_add, Submodule.coe_add] at *`.

Conclude with `Submodule.add_mem _ hu hv`. Use the proof step `zero_mem' := by simp`. Use the proof step `smul_mem' := by`. Introduce `a u hu`. Simplify using `only [Set.mem_setOf_eq] at *`.

Rewrite using `[he, smul_val]`. Conclude with `Submodule.sum_mem _ (fun κ _ => Submodule.smul_mem _ _ (hstab κ κ.2 _ hu)) }`. Establish `hWmem : ∀ u, u ∈ W ↔ ((e u : D) : V) ∈ Sb` using `fun u => Iff.rfl`. Take `⟨C, hC⟩` from `exists_isCompl W`. Set `π` to `W.subtype ∘ₗ W.projectionOnto C hC`.

Establish `hπW : ∀ u ∈ W, π u = u` using `fun u hu => by show ((W.projectionOnto C hC ((⟨u, hu⟩ : W) : _)) : _) = u`. Rewrite using `[Submodule.projectionOnto_apply_left]`. Establish `hπmem : ∀ u, π u ∈ W` using `fun u => (W.projectionOnto C hC u).2`. Establish `hPW : ∀ u ∈ W, P u ∈ W` using `fun u hu => by`. Rewrite using `[← hπW u hu, hPc π]`.

Conclude with `hπmem _`. Set `Bs` to `Module.Basis.span hli`. Establish `hBs : ∀ j, ((Bs j : Sb) : V) = b j` using `fun j => by simp [Bs, Module.Basis.span_apply]`. Set `incl : Sb →ₗ[ℂ] D` to `Submodule.inclusion hSbD`. Establish `hinclBs : ∀ j, incl (Bs j) = ⟨b j, hbD j⟩` using `fun j => Subtype.ext (hBs j)`.

Set `ρS : ∀ k ∈ K, Sb →ₗ[ℂ] Sb` to `fun k hk => (ρ k).restrict (hstab k hk)`. Establish `hρS : ∀ k (hk : k ∈ K), ρS k hk = Matrix.toLin Bs Bs (A k)`. Introduce `k hk`. Use `Bs.ext (fun j => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.toLin_self]`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[ρS, LinearMap.restrict_apply, hBs, hAct k hk j]`. Establish `hTPmem : ∀ x : Sb, ((e (P (e.symm (incl x))) : D) : V) ∈ Sb` using `fun x => by`. Establish `: e.symm (incl x) ∈ W` using `by rw [hWmem]; simp [incl]`. Conclude with `hPW _ this`.

Set `TP : Sb →ₗ[ℂ] Sb` to `LinearMap.codRestrict Sb (D.subtype ∘ₗ (toEndD ρ D K h1 hmul hst P) ∘ₗ incl) hTPmem`. Establish `hTP : ∀ x, ((TP x : Sb) : V) = ((e (P (e.symm (incl x))) : D) : V)` using `fun x => rfl`. Set `Pm` to `LinearMap.toMatrix Bs Bs TP`. Establish `hform : ∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ∑ i, Pm i j • b i`. Introduce `j`.

Establish `h1' : ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ((TP (Bs j) : Sb) : V)`. Rewrite using `[hTP, hinclBs]`. Both sides reduce to the same expression. Rewrite using `[h1']`. Use `conv_lhs => rw [← Matrix.toLin_toMatrix Bs Bs TP]`.

Rewrite using `[Matrix.toLin_self]`. Simplify using `[hBs, Pm]`. Establish `hinclTP : ∀ x, incl (TP x) = e (P (e.symm (incl x)))` using `fun x => Subtype.ext (hTP x)`. Establish `hidem : Pm * Pm = Pm`. Establish `h : TP ∘ₗ TP = TP`.

Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Use `show ((TP (TP x) : Sb) : V) = ((TP x : Sb) : V)`. Rewrite using `[hTP, hinclTP, LinearEquiv.symm_apply_apply, hPP]`. Conclude with `(hTP x).symm`. Combine the equalities or inequalities in the displayed calculation.

Establish `hmatA : ∀ k (hk : k ∈ K), LinearMap.toMatrix Bs Bs (ρS k hk) = A k` using `fun k hk => by`. Rewrite using `[hρS k hk, LinearMap.toMatrix_toLin]`. Establish `hcommA : ∀ k ∈ K, Pm * A k = A k * Pm`. Introduce `k hk`. Establish `h : TP ∘ₗ ρS k hk = ρS k hk ∘ₗ TP`.

Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Use `show ((TP (ρS k hk x) : Sb) : V) = ρ k ((TP x : Sb) : V)`. Rewrite using `[hTP, hTP]`. Establish `h2 : incl (ρS k hk x) = (repD ρ D K h1 hmul hst ⟨k, hk⟩) (incl x)` using `Subtype.ext rfl`. Rewrite using `[h2, he, Representation.asModuleEquiv_symm_map_rho, P.map_smul, Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]`.

Both sides reduce to the same expression. Rewrite using `[← hmatA k hk, ← LinearMap.toMatrix_comp Bs Bs Bs, h, LinearMap.toMatrix_comp Bs Bs Bs]`. Establish `hcommQ : ∀ Q : Matrix (Fin m) (Fin m) ℂ, (∀ k ∈ K, Q * A k = A k * Q) → Pm * Q = Q * Pm`. Introduce `Q hQ`. Set `LQ` to `Matrix.toLin Bs Bs Q`.

Establish `hLQ : ∀ k (hk : k ∈ K) x, LQ (ρS k hk x) = ρS k hk (LQ x)`. Introduce `k hk x`. Rewrite using `[hρS k hk]`. Use `show (LQ ∘ₗ Matrix.toLin Bs Bs (A k)) x = (Matrix.toLin Bs Bs (A k) ∘ₗ LQ) x`. Rewrite using `[← Matrix.toLin_mul Bs Bs Bs, ← Matrix.toLin_mul Bs Bs Bs, hQ k hk]`.

Establish `hsmulV : ∀ (a : MonoidAlgebra ℂ (subK K h1 hmul)) (y : (repD ρ D K h1 hmul hst).asModule), ((e (a • y) : D) : V) = ∑ κ ∈ a.coeff.support, a.coeff κ • ρ κ ((e y : D) : V)` using `fun a y => smul_val ρ D K h1 hmul hst a y`. Set `g : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)] (repD ρ D K h1 hmul hst).asModule` to `{ toFun := fun u => e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩)) map_add' := by`. Introduce `u v`. Establish `h : (⟨((e (π (u + v)) : D) : V), hπmem (u + v)⟩ : Sb) = ⟨((e (π u) : D) : V), hπmem u⟩ + ⟨((e (π v) : D) : V), hπmem v⟩` using `Subtype.ext (by simp)`. Use `show e.symm (incl (LQ ⟨((e (π (u + v)) : D) : V), hπmem (u + v)⟩)) = e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩)) + e.symm (incl (LQ ⟨((e (π v) : D) : V), hπmem v⟩))`.

Rewrite using `[h, map_add, map_add, map_add]`. Use the proof step `map_smul' := by`. Introduce `a u`. Apply `e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show ((e (e.symm (incl (LQ ⟨((e (π (a • u)) : D) : V), hπmem (a • u)⟩)))) : V) = ((e (a • e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩)))) : V)`. Rewrite using `[hsmulV, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Establish `key : (⟨((e (π (a • u)) : D) : V), hπmem (a • u)⟩ : Sb) = ∑ κ ∈ a.coeff.support, a.coeff κ • ρS κ κ.2 ⟨((e (π u) : D) : V), hπmem u⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum]`.

Simplify using `only [Submodule.coe_smul, ρS, LinearMap.restrict_apply]`. Use `show ((e (π (a • u)) : D) : V) = _`. Rewrite using `[π.map_smul a u, hsmulV]`. Rewrite using `[key, map_sum]`. Simplify using `only [map_smul, hLQ]`.

Rewrite using `[map_sum, Submodule.coe_sum]`. Simplify using `only [map_smul, Submodule.coe_smul]`. Use `Finset.sum_congr rfl (fun κ _ => ?_)` and prove the remaining obligations. Rewrite using `[hLQ κ κ.2]`. Use `rfl }`.

Establish `hg : ∀ w (hw : w ∈ W), g w = e.symm (incl (LQ ⟨((e w : D) : V), hw⟩))`. Introduce `w hw`. Establish `h : (⟨((e (π w) : D) : V), hπmem w⟩ : Sb) = ⟨((e w : D) : V), hw⟩` using `Subtype.ext (by simp only [hπW w hw])`. Use `show e.symm (incl (LQ ⟨((e (π w) : D) : V), hπmem w⟩)) = _`. Rewrite using `[h]`.

Establish `hcomm : TP ∘ₗ LQ = LQ ∘ₗ TP`. Use `LinearMap.ext fun x => Subtype.ext ?_` and prove the remaining obligations. Use `show ((TP (LQ x) : Sb) : V) = ((LQ (TP x) : Sb) : V)`. Establish `hx : e.symm (incl x) ∈ W` using `by rw [hWmem]; simp [incl]`. Establish `hgx : g (e.symm (incl x)) = e.symm (incl (LQ x))`.

Rewrite using `[hg _ hx]`. Use `congr 3`. Establish `hgP : g (P (e.symm (incl x))) = e.symm (incl (LQ (TP x)))`. Rewrite using `[hg _ (hPW _ hx)]`. Use `congr 3`.

Rewrite using `[hTP, ← hgx, hPc g, hgP, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression. Establish `hmQ : LinearMap.toMatrix Bs Bs LQ = Q` using `LinearMap.toMatrix_toLin Bs Bs Q`. Rewrite using `[← hmQ, ← LinearMap.toMatrix_comp Bs Bs Bs, hcomm, LinearMap.toMatrix_comp Bs Bs Bs]`. Establish `hstarA : ∀ k ∈ K, star Pm * A k = A k * star Pm`.

Introduce `k hk`. Establish `hu1 : A k * star (A k) = 1` using `Matrix.mem_unitaryGroup_iff.1 (hU k hk)`. Establish `hu2 : star (A k) * A k = 1` using `Matrix.mem_unitaryGroup_iff'.1 (hU k hk)`. Establish `hs : star (A k) * star Pm = star Pm * star (A k)`. Rewrite using `[← star_mul, ← star_mul, hcommA k hk]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hnorm : Pm * star Pm = star Pm * Pm` using `hcommQ (star Pm) hstarA`. Establish `hss' : star Pm * star Pm = star Pm` using `by rw [← star_mul, hidem]`. Use `set N := Pm - star Pm * Pm with hN`. Establish `hNs : star N = star Pm - star Pm * Pm`.

Rewrite using `[hN, star_sub, star_mul, star_star]`. Establish `hNN : star N * N = 0`. Rewrite using `[hNs, hN]`. Establish `e1 : star Pm * Pm * Pm = star Pm * Pm` using `by rw [mul_assoc, hidem]`. Establish `e2 : star Pm * (star Pm * Pm) = star Pm * Pm` using `by rw [← mul_assoc, hss']`.

Establish `e3 : star Pm * Pm * (star Pm * Pm) = star Pm * Pm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[sub_mul, mul_sub, mul_sub, e1, e2, e3]`. Normalize the expressions using the abelian group laws. Establish `hN0 : N = 0`.

Rewrite `hNN` using `[Matrix.star_eq_conjTranspose]`. Use `open scoped ComplexOrder in exact Matrix.conjTranspose_mul_self_eq_zero.1 hNN`. Establish `hPm : Pm = star Pm * Pm` using `sub_eq_zero.1 (hN ▸ hN0)`. Use `⟨Pm, hform, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem GlobalTheory.LocFinIso.hermitian_matrix_of_commuting_idempotent : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (h1 : (1 : G) ∈ K) (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D), IsSemisimpleModule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule → ∀ (P : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)] (repD ρ D K h1 hmul hst).asModule), (∀ v, P (P v) = P v) → (∀ g : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)] (repD ρ D K h1 hmul hst).asModule, ∀ v, P (g v) = g (P v)) → ∀ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ) (hbD : ∀ i, b i ∈ D), LinearIndependent ℂ b → (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) → (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) → ∃ Pm : Matrix (Fin m) (Fin m) ℂ, (∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ∑ i, Pm i j • b i) ∧ star Pm = Pm := by
  intro G _ K V _ _ ρ D h1 hmul hst hss P hPP hPc m b A hbD hli hAct hU
  haveI := hss
  set e := (repD ρ D K h1 hmul hst).asModuleEquiv with he
  set Sb : Submodule ℂ V := Submodule.span ℂ (Set.range b) with hSb
  have hSbD : Sb ≤ D := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hbD i)
  have hstab : ∀ k ∈ K, ∀ x ∈ Sb, ρ k x ∈ Sb := by
    intro k hk x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      rw [hAct k hk j]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  let W : Submodule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule :=
    { carrier := {u | ((e u : D) : V) ∈ Sb}
      add_mem' := by
        intro u v hu hv
        simp only [Set.mem_setOf_eq, map_add, Submodule.coe_add] at *
        exact Submodule.add_mem _ hu hv
      zero_mem' := by simp
      smul_mem' := by
        intro a u hu
        simp only [Set.mem_setOf_eq] at *
        rw [he, smul_val]
        exact Submodule.sum_mem _ (fun κ _ => Submodule.smul_mem _ _ (hstab κ κ.2 _ hu)) }
  have hWmem : ∀ u, u ∈ W ↔ ((e u : D) : V) ∈ Sb := fun u => Iff.rfl
  obtain ⟨C, hC⟩ := exists_isCompl W
  let π := W.subtype ∘ₗ W.projectionOnto C hC
  have hπW : ∀ u ∈ W, π u = u := fun u hu => by
    show ((W.projectionOnto C hC ((⟨u, hu⟩ : W) : _)) : _) = u
    rw [Submodule.projectionOnto_apply_left]
  have hπmem : ∀ u, π u ∈ W := fun u => (W.projectionOnto C hC u).2
  have hPW : ∀ u ∈ W, P u ∈ W := fun u hu => by
    rw [← hπW u hu, hPc π]; exact hπmem _

  let Bs := Module.Basis.span hli
  have hBs : ∀ j, ((Bs j : Sb) : V) = b j := fun j => by simp [Bs, Module.Basis.span_apply]
  let incl : Sb →ₗ[ℂ] D := Submodule.inclusion hSbD
  have hinclBs : ∀ j, incl (Bs j) = ⟨b j, hbD j⟩ := fun j => Subtype.ext (hBs j)
  let ρS : ∀ k ∈ K, Sb →ₗ[ℂ] Sb := fun k hk => (ρ k).restrict (hstab k hk)
  have hρS : ∀ k (hk : k ∈ K), ρS k hk = Matrix.toLin Bs Bs (A k) := by
    intro k hk
    refine Bs.ext (fun j => ?_)
    rw [Matrix.toLin_self]
    apply Subtype.ext
    simp [ρS, LinearMap.restrict_apply, hBs, hAct k hk j]
  have hTPmem : ∀ x : Sb, ((e (P (e.symm (incl x))) : D) : V) ∈ Sb := fun x => by
    have : e.symm (incl x) ∈ W := by rw [hWmem]; simp [incl]
    exact hPW _ this
  let TP : Sb →ₗ[ℂ] Sb :=
    LinearMap.codRestrict Sb (D.subtype ∘ₗ (toEndD ρ D K h1 hmul hst P) ∘ₗ incl) hTPmem
  have hTP : ∀ x, ((TP x : Sb) : V) = ((e (P (e.symm (incl x))) : D) : V) := fun x => rfl
  let Pm := LinearMap.toMatrix Bs Bs TP
  have hform : ∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ∑ i, Pm i j • b i := by
    intro j
    have h1' : ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ((TP (Bs j) : Sb) : V) := by
      rw [hTP, hinclBs]; rfl
    rw [h1']
    conv_lhs => rw [← Matrix.toLin_toMatrix Bs Bs TP]
    rw [Matrix.toLin_self]
    simp [hBs, Pm]

  have hinclTP : ∀ x, incl (TP x) = e (P (e.symm (incl x))) := fun x => Subtype.ext (hTP x)
  have hidem : Pm * Pm = Pm := by
    have h : TP ∘ₗ TP = TP := by
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ((TP (TP x) : Sb) : V) = ((TP x : Sb) : V)
      rw [hTP, hinclTP, LinearEquiv.symm_apply_apply, hPP]
      exact (hTP x).symm
    calc Pm * Pm = LinearMap.toMatrix Bs Bs (TP ∘ₗ TP) := (LinearMap.toMatrix_comp Bs Bs Bs TP TP).symm
      _ = Pm := by rw [h]
  have hmatA : ∀ k (hk : k ∈ K), LinearMap.toMatrix Bs Bs (ρS k hk) = A k := fun k hk => by
    rw [hρS k hk, LinearMap.toMatrix_toLin]
  have hcommA : ∀ k ∈ K, Pm * A k = A k * Pm := by
    intro k hk
    have h : TP ∘ₗ ρS k hk = ρS k hk ∘ₗ TP := by
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ((TP (ρS k hk x) : Sb) : V) = ρ k ((TP x : Sb) : V)
      rw [hTP, hTP]
      have h2 : incl (ρS k hk x) = (repD ρ D K h1 hmul hst ⟨k, hk⟩) (incl x) := Subtype.ext rfl
      rw [h2, he, Representation.asModuleEquiv_symm_map_rho, P.map_smul,
        Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
      rfl
    rw [← hmatA k hk, ← LinearMap.toMatrix_comp Bs Bs Bs, h, LinearMap.toMatrix_comp Bs Bs Bs]

  have hcommQ : ∀ Q : Matrix (Fin m) (Fin m) ℂ, (∀ k ∈ K, Q * A k = A k * Q) → Pm * Q = Q * Pm := by
    intro Q hQ
    let LQ := Matrix.toLin Bs Bs Q
    have hLQ : ∀ k (hk : k ∈ K) x, LQ (ρS k hk x) = ρS k hk (LQ x) := by
      intro k hk x
      rw [hρS k hk]
      show (LQ ∘ₗ Matrix.toLin Bs Bs (A k)) x = (Matrix.toLin Bs Bs (A k) ∘ₗ LQ) x
      rw [← Matrix.toLin_mul Bs Bs Bs, ← Matrix.toLin_mul Bs Bs Bs, hQ k hk]
    have hsmulV : ∀ (a : MonoidAlgebra ℂ (subK K h1 hmul)) (y : (repD ρ D K h1 hmul hst).asModule),
        ((e (a • y) : D) : V) = ∑ κ ∈ a.coeff.support, a.coeff κ • ρ κ ((e y : D) : V) :=
      fun a y => smul_val ρ D K h1 hmul hst a y
    let g : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)]
        (repD ρ D K h1 hmul hst).asModule :=
      { toFun := fun u => e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩))
        map_add' := by
          intro u v
          have h : (⟨((e (π (u + v)) : D) : V), hπmem (u + v)⟩ : Sb) =
              ⟨((e (π u) : D) : V), hπmem u⟩ + ⟨((e (π v) : D) : V), hπmem v⟩ :=
            Subtype.ext (by simp)
          show e.symm (incl (LQ ⟨((e (π (u + v)) : D) : V), hπmem (u + v)⟩)) =
            e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩)) + e.symm (incl (LQ ⟨((e (π v) : D) : V), hπmem v⟩))
          rw [h, map_add, map_add, map_add]
        map_smul' := by
          intro a u
          apply e.injective
          apply Subtype.ext
          show ((e (e.symm (incl (LQ ⟨((e (π (a • u)) : D) : V), hπmem (a • u)⟩)))) : V) =
            ((e (a • e.symm (incl (LQ ⟨((e (π u) : D) : V), hπmem u⟩)))) : V)
          rw [hsmulV, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
          have key : (⟨((e (π (a • u)) : D) : V), hπmem (a • u)⟩ : Sb) =
              ∑ κ ∈ a.coeff.support, a.coeff κ • ρS κ κ.2 ⟨((e (π u) : D) : V), hπmem u⟩ := by
            apply Subtype.ext
            rw [Submodule.coe_sum]
            simp only [Submodule.coe_smul, ρS, LinearMap.restrict_apply]
            show ((e (π (a • u)) : D) : V) = _
            rw [π.map_smul a u, hsmulV]
          rw [key, map_sum]
          simp only [map_smul, hLQ]
          rw [map_sum, Submodule.coe_sum]
          simp only [map_smul, Submodule.coe_smul]
          refine Finset.sum_congr rfl (fun κ _ => ?_)
          rw [hLQ κ κ.2]
          rfl }
    have hg : ∀ w (hw : w ∈ W), g w = e.symm (incl (LQ ⟨((e w : D) : V), hw⟩)) := by
      intro w hw
      have h : (⟨((e (π w) : D) : V), hπmem w⟩ : Sb) = ⟨((e w : D) : V), hw⟩ :=
        Subtype.ext (by simp only [hπW w hw])
      show e.symm (incl (LQ ⟨((e (π w) : D) : V), hπmem w⟩)) = _
      rw [h]
    have hcomm : TP ∘ₗ LQ = LQ ∘ₗ TP := by
      refine LinearMap.ext fun x => Subtype.ext ?_
      show ((TP (LQ x) : Sb) : V) = ((LQ (TP x) : Sb) : V)
      have hx : e.symm (incl x) ∈ W := by rw [hWmem]; simp [incl]
      have hgx : g (e.symm (incl x)) = e.symm (incl (LQ x)) := by
        rw [hg _ hx]; congr 3
      have hgP : g (P (e.symm (incl x))) = e.symm (incl (LQ (TP x))) := by
        rw [hg _ (hPW _ hx)]; congr 3
      rw [hTP, ← hgx, hPc g, hgP, LinearEquiv.apply_symm_apply]
      rfl
    have hmQ : LinearMap.toMatrix Bs Bs LQ = Q := LinearMap.toMatrix_toLin Bs Bs Q
    rw [← hmQ, ← LinearMap.toMatrix_comp Bs Bs Bs, hcomm, LinearMap.toMatrix_comp Bs Bs Bs]

  have hstarA : ∀ k ∈ K, star Pm * A k = A k * star Pm := by
    intro k hk
    have hu1 : A k * star (A k) = 1 := Matrix.mem_unitaryGroup_iff.1 (hU k hk)
    have hu2 : star (A k) * A k = 1 := Matrix.mem_unitaryGroup_iff'.1 (hU k hk)
    have hs : star (A k) * star Pm = star Pm * star (A k) := by
      rw [← star_mul, ← star_mul, hcommA k hk]
    calc star Pm * A k = (A k * star (A k)) * star Pm * A k := by rw [hu1, one_mul]
      _ = A k * (star (A k) * star Pm) * A k := by simp only [mul_assoc]
      _ = A k * (star Pm * star (A k)) * A k := by rw [hs]
      _ = A k * star Pm * (star (A k) * A k) := by simp only [mul_assoc]
      _ = A k * star Pm := by rw [hu2, mul_one]
  have hnorm : Pm * star Pm = star Pm * Pm := hcommQ (star Pm) hstarA
  have hss' : star Pm * star Pm = star Pm := by rw [← star_mul, hidem]
  set N := Pm - star Pm * Pm with hN
  have hNs : star N = star Pm - star Pm * Pm := by
    rw [hN, star_sub, star_mul, star_star]
  have hNN : star N * N = 0 := by
    rw [hNs, hN]
    have e1 : star Pm * Pm * Pm = star Pm * Pm := by rw [mul_assoc, hidem]
    have e2 : star Pm * (star Pm * Pm) = star Pm * Pm := by rw [← mul_assoc, hss']
    have e3 : star Pm * Pm * (star Pm * Pm) = star Pm * Pm := by
      calc star Pm * Pm * (star Pm * Pm) = star Pm * (Pm * star Pm) * Pm := by simp only [mul_assoc]
        _ = star Pm * (star Pm * Pm) * Pm := by rw [hnorm]
        _ = star Pm * Pm := by rw [e2, e1]
    rw [sub_mul, mul_sub, mul_sub, e1, e2, e3]
    abel
  have hN0 : N = 0 := by
    rw [Matrix.star_eq_conjTranspose] at hNN
    open scoped ComplexOrder in exact Matrix.conjTranspose_mul_self_eq_zero.1 hNN
  have hPm : Pm = star Pm * Pm := sub_eq_zero.1 (hN ▸ hN0)
  refine ⟨Pm, hform, ?_⟩
  calc star Pm = star (star Pm * Pm) := by rw [← hPm]
    _ = star Pm * Pm := by rw [star_mul, star_star]
    _ = Pm := hPm.symm
