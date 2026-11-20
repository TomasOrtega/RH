import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerCocyclesScalarChangeTransferStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenNormalSubgroupUnderInertia

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.UnivCocycle

/- English proof (translation)
Use function extensionality and compare the values at `c`. Simplify using `[matAct, h]`.
-/
theorem matAct_map {Λ B Y : Type} [CommRing Λ] [CommRing B] [AddCommGroup Y] [Module Λ Y] [Module B Y] (φ : Λ → B)
    (h : ∀ (c : Λ) (y : Y), c • y = φ c • y) {a : ℕ} (Φ : Matrix (Fin a) (Fin a) Λ) (x : Fin a → Y) :
    matAct Φ x = matAct (Φ.map φ) x := by
  funext c
  simp [matAct, h]

def ev {B Y : Type} [CommRing B] [AddCommGroup Y] [Module B Y] {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) B) (x : Fin a → Y)
    (hx : matAct Ψ x = 0) : ((Fin a → B) ⧸ what₂ Ψ) →ₗ[B] Y :=
  (what₂ Ψ).liftQ (Fintype.linearCombination B x) (by
    rw [Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    have := congrFun hx c
    simpa [matAct, Fintype.linearCombination_apply] using this)

/- English proof (translation)
Simplify using `[ev, Fintype.linearCombination_apply]`.
-/
theorem ev_mk {B Y : Type} [CommRing B] [AddCommGroup Y] [Module B Y] {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) B) (x : Fin a → Y)
    (hx : matAct Ψ x = 0) (v : Fin a → B) : ev Ψ x hx (Submodule.Quotient.mk v) = ∑ j, v j • x j := by
  simp [ev, Fintype.linearCombination_apply]

/- English proof (translation)
Use function extensionality and compare the values at `c`. Establish `h : (∑ j, Ψ c j • (Pi.single j 1 : Fin a → B)) = Ψ c`. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `h2 : (Submodule.Quotient.mk (Ψ c) : (Fin a → B) ⧸ what₂ Ψ) = 0` using `(Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨c, rfl⟩)`.

Rewrite `h2` using `[← h, ← Submodule.mkQ_apply, map_sum]`. Simplify `h2` using `[matAct]`.
-/
theorem univ_ker {B : Type} [CommRing B] {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) B) :
    matAct Ψ (fun j => (Submodule.Quotient.mk (Pi.single j 1) : (Fin a → B) ⧸ what₂ Ψ)) = 0 := by
  funext c
  have h : (∑ j, Ψ c j • (Pi.single j 1 : Fin a → B)) = Ψ c := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : (Submodule.Quotient.mk (Ψ c) : (Fin a → B) ⧸ what₂ Ψ) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨c, rfl⟩)
  rw [← h, ← Submodule.mkQ_apply, map_sum] at h2
  simpa [matAct] using h2

/- English proof (translation)
Use `⟨nu X i + 1, ?_⟩` and prove the remaining obligations. Establish `h` using `hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i)) (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.ResSel.SmallSub.l_mem X i))`. Rewrite `h` using `[map_mul, map_pow, map_natCast]`. Rewrite using `[← Nat.cast_smul_eq_nsmul B, Nat.cast_pow, pow_succ, h, zero_smul]`.
-/
theorem tors {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw)
    {B : Type} [CommRing B] [Algebra (X.O0 i) B] (hK : Kills i B) (Y : Type) [AddCommGroup Y] [Module B Y] (b : Y) :
    ∃ n : ℕ, (X.l i ^ n) • b = 0 := by
  refine ⟨nu X i + 1, ?_⟩
  have h := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
    (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.ResSel.SmallSub.l_mem X i))
  rw [map_mul, map_pow, map_natCast] at h
  rw [← Nat.cast_smul_eq_nsmul B, Nat.cast_pow, pow_succ, h, zero_smul]

/- English proof (translation)
Introduce `D N X bkP i s M ι d Q a Φ hC B _ _ φ κ hκ hK`. Take `⟨e, he⟩` from `hC`. Use `letI : TopologicalSpace ((Fin a → B) ⧸ what₂ (Φ.map φ)) := ⊥`. Use `haveI : DiscreteTopology ((Fin a → B) ⧸ what₂ (Φ.map φ)) := ⟨rfl⟩`. Use `letI : Module (abelian₂ X i M ι) ((Fin a → B) ⧸ what₂ (Φ.map φ)) := Module.compHom _ (φ : abelian₂ X i M ι →+* B)`.

Establish `hW : ∀ (c : abelian₂ X i M ι) (y : (Fin a → B) ⧸ what₂ (Φ.map φ)), c • y = φ c • y` using `fun _ _ => rfl`. Set `xu : LinearMap.ker (matAct (M` to `(Fin a → B) ⧸ what₂ (Φ.map φ)) Φ) := ⟨fun j => Submodule.Quotient.mk (Pi.single j 1), by`. Rewrite using `[LinearMap.mem_ker, matAct_map φ hW]`. Conclude with `univ_ker _⟩`. Take `⟨z, hz⟩` from `Submodule.Quotient.mk_surjective _ (e _ (tors i hK _) xu).1`.

Use `choose Z hZ using fun g c => Submodule.Quotient.mk_surjective (what₂ (Φ.map φ)) (z.1 g c)`. Use `⟨fun g => Matrix.of (Z g), ?_⟩` and prove the remaining obligations. Introduce `Y _ _ _ _`. Use `letI : Module (abelian₂ X i M ι) Y := Module.compHom _ (φ : abelian₂ X i M ι →+* B)`. Establish `hY : ∀ (c : abelian₂ X i M ι) (y : Y), c • y = φ c • y` using `fun _ _ => rfl`.

Take `⟨hrep, hsel⟩` from `GlobalTheory.T.selmerCocycles_scalarChange_transfer D N X bkP i s _ B φ (delInv i M d) κ hκ Y hY`. Establish `key : ∀ x : LinearMap.ker (matAct (M` using `Y) Φ), ∃ z' : Z1 (repOn (Tgl i s) (delInv i M d) Y), z'.1 = (fun g => rect (Matrix.of (Z g)) x.1) ∧ (e Y (tors i hK Y) x).1 = Submodule.Quotient.mk z' := by`. Introduce `x`. Establish `hx : matAct (Φ.map φ) x.1 = 0` using `by rw [← matAct_map φ hY]; exact x.2`. Set `f : ((Fin a → B) ⧸ what₂ (Φ.map φ)) →ₗ[abelian₂ X i M ι] Y` to `{ toFun := ev _ x.1 hx map_add' := map_add _ map_smul' := fun c y => by rw [hW, map_smul, RingHom.id_apply, hY] }`.

Establish `hf : ∀ v, f (Submodule.Quotient.mk v) = ∑ j, v j • x.1 j` using `ev_mk _ _ hx`. Use `⟨cocycles1MapOfEquivariant _ _ (f.compLeft (Fin D.R.r)) continuous_of_discreteTopology (repOn_map _ _ f) z, ?_, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g c`. Express the relevant statement in the definitionally equal form `f (z.1 g c) = _`. Rewrite using `[← hZ, hf]`.

Both sides reduce to the same expression. Use `he _ Y _ _ f xu x z _ (fun c => ?_) (fun g c => rfl) hz.symm` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = f (Submodule.Quotient.mk _)`. Rewrite using `[hf]`. Simplify using `[Pi.single_apply]`.

Establish `hker : ∀ x : Fin a → Y, matAct (Φ.map φ) x = 0 → x ∈ LinearMap.ker (matAct (M` using `Y) Φ) := fun x hx => by`. Rewrite using `[LinearMap.mem_ker, matAct_map φ hY]`. Conclude with `hx`. Use `⟨fun x hx => ?_, fun x hx hc => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Take `⟨z', h1, h2⟩` from `key ⟨x, hker x hx⟩`.

Conclude with `(hsel Q _).1 ⟨z', h1, h2 ▸ (e Y (tors i hK Y) ⟨x, hker x hx⟩).2⟩`. Take `⟨z', h1, h2⟩` from `key ⟨x, hker x hx⟩`. Take `⟨m, hm⟩` from `hc`. Establish `h0 : (Submodule.Quotient.mk z' : H1 (repOn (Tgl i s) (delInv i M d) Y)) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]`.

Use `⟨m, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hrep, ← hm]`. Conclude with `congrFun h1 g`. Establish `h3 : e Y (tors i hK Y) ⟨x, hker x hx⟩ = 0` using `Subtype.ext (h2.trans h0)`. Conclude with `congrArg Subtype.val ((e Y (tors i hK Y)).map_eq_zero_iff.1 h3)`.

Take `⟨w, rfl, hw⟩` from `(hsel Q f).2 hf`. Take `⟨x, hx⟩` from `(e Y (tors i hK Y)).surjective ⟨_, hw⟩`. Take `⟨z', h1, h2⟩` from `key x`. Use `⟨x.1, by rw [← matAct_map φ hY]; exact x.2, ?_⟩` and prove the remaining obligations. Establish `h3 : (Submodule.Quotient.mk w : H1 (repOn (Tgl i s) (delInv i M d) Y)) = Submodule.Quotient.mk z'`.

Rewrite using `[← h2, hx]`. Rewrite `h3` using `[Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1]`. Take `⟨m, hm⟩` from `h3`. Use `⟨m, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← hrep, ← hm]`.

Express the relevant statement in the definitionally equal form `_ = w.1 g - z'.1 g`. Rewrite using `[h1]`.
-/
theorem main : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (M : ℕ) (ι : Type) (d : ι → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) (abelian₂ X i M ι)), Computes bkP i s M d Q Φ → ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (φ : abelian₂ X i M ι →ₐ[X.O0 i] B) (κ : GE N →* Bˣ), (∀ g, ((κ g : Bˣ) : B) = φ (delInv i M d g : (abelian₂ X i M ι)ˣ)) → Kills i B → ∃ Z, Univ bkP i s κ Q (Φ.map φ) Z := by
  intro D N X bkP i s M ι d Q a Φ hC B _ _ φ κ hκ hK
  obtain ⟨e, he⟩ := hC
  letI : TopologicalSpace ((Fin a → B) ⧸ what₂ (Φ.map φ)) := ⊥
  haveI : DiscreteTopology ((Fin a → B) ⧸ what₂ (Φ.map φ)) := ⟨rfl⟩
  letI : Module (abelian₂ X i M ι) ((Fin a → B) ⧸ what₂ (Φ.map φ)) := Module.compHom _ (φ : abelian₂ X i M ι →+* B)
  have hW : ∀ (c : abelian₂ X i M ι) (y : (Fin a → B) ⧸ what₂ (Φ.map φ)), c • y = φ c • y := fun _ _ => rfl
  let xu : LinearMap.ker (matAct (M := (Fin a → B) ⧸ what₂ (Φ.map φ)) Φ) :=
    ⟨fun j => Submodule.Quotient.mk (Pi.single j 1), by
      rw [LinearMap.mem_ker, matAct_map φ hW]; exact univ_ker _⟩
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (e _ (tors i hK _) xu).1
  choose Z hZ using fun g c => Submodule.Quotient.mk_surjective (what₂ (Φ.map φ)) (z.1 g c)
  refine ⟨fun g => Matrix.of (Z g), ?_⟩
  intro Y _ _ _ _
  letI : Module (abelian₂ X i M ι) Y := Module.compHom _ (φ : abelian₂ X i M ι →+* B)
  have hY : ∀ (c : abelian₂ X i M ι) (y : Y), c • y = φ c • y := fun _ _ => rfl
  obtain ⟨hrep, hsel⟩ := GlobalTheory.T.selmerCocycles_scalarChange_transfer D N X bkP i s _ B φ (delInv i M d) κ hκ Y hY
  have key : ∀ x : LinearMap.ker (matAct (M := Y) Φ), ∃ z' : Z1 (repOn (Tgl i s) (delInv i M d) Y),
      z'.1 = (fun g => rect (Matrix.of (Z g)) x.1) ∧ (e Y (tors i hK Y) x).1 = Submodule.Quotient.mk z' := by
    intro x
    have hx : matAct (Φ.map φ) x.1 = 0 := by rw [← matAct_map φ hY]; exact x.2
    let f : ((Fin a → B) ⧸ what₂ (Φ.map φ)) →ₗ[abelian₂ X i M ι] Y :=
      { toFun := ev _ x.1 hx
        map_add' := map_add _
        map_smul' := fun c y => by rw [hW, map_smul, RingHom.id_apply, hY] }
    have hf : ∀ v, f (Submodule.Quotient.mk v) = ∑ j, v j • x.1 j := ev_mk _ _ hx
    refine ⟨cocycles1MapOfEquivariant _ _ (f.compLeft (Fin D.R.r)) continuous_of_discreteTopology (repOn_map _ _ f) z, ?_, ?_⟩
    · funext g c
      change f (z.1 g c) = _
      rw [← hZ, hf]
      rfl
    · refine he _ Y _ _ f xu x z _ (fun c => ?_) (fun g c => rfl) hz.symm
      change _ = f (Submodule.Quotient.mk _)
      rw [hf]
      simp [Pi.single_apply]
  have hker : ∀ x : Fin a → Y, matAct (Φ.map φ) x = 0 → x ∈ LinearMap.ker (matAct (M := Y) Φ) := fun x hx => by
    rw [LinearMap.mem_ker, matAct_map φ hY]; exact hx
  refine ⟨fun x hx => ?_, fun x hx hc => ?_, fun f hf => ?_⟩
  · obtain ⟨z', h1, h2⟩ := key ⟨x, hker x hx⟩
    exact (hsel Q _).1 ⟨z', h1, h2 ▸ (e Y (tors i hK Y) ⟨x, hker x hx⟩).2⟩
  · obtain ⟨z', h1, h2⟩ := key ⟨x, hker x hx⟩
    obtain ⟨m, hm⟩ := hc
    have h0 : (Submodule.Quotient.mk z' : H1 (repOn (Tgl i s) (delInv i M d) Y)) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, mem_coboundaries1]
      refine ⟨m, fun g => ?_⟩
      rw [hrep, ← hm]
      exact congrFun h1 g
    have h3 : e Y (tors i hK Y) ⟨x, hker x hx⟩ = 0 := Subtype.ext (h2.trans h0)
    exact congrArg Subtype.val ((e Y (tors i hK Y)).map_eq_zero_iff.1 h3)
  · obtain ⟨w, rfl, hw⟩ := (hsel Q f).2 hf
    obtain ⟨x, hx⟩ := (e Y (tors i hK Y)).surjective ⟨_, hw⟩
    obtain ⟨z', h1, h2⟩ := key x
    refine ⟨x.1, by rw [← matAct_map φ hY]; exact x.2, ?_⟩
    have h3 : (Submodule.Quotient.mk w : H1 (repOn (Tgl i s) (delInv i M d) Y)) = Submodule.Quotient.mk z' := by
      rw [← h2, hx]
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at h3
    obtain ⟨m, hm⟩ := h3
    refine ⟨m, fun g => ?_⟩
    rw [← hrep, ← hm]
    change _ = w.1 g - z'.1 g
    rw [h1]

end GlobalTheory.NewPrime.UnivCocycle
