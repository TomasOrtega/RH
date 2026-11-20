import Mathlib
open NumberField

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem dvd_functional_of_basis {M ι : Type*} [AddCommGroup M] (b : Module.Basis ι ℤ M)
    (N : ℕ) (g : M →+ ℤ) (h : ∀ k, (N : ℤ) ∣ g (b k)) (c : M) : (N : ℤ) ∣ g c := by
  have hc : c ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact dvd_add hx hy
  | smul a x _ hx => rw [map_zsmul, smul_eq_mul]; exact Dvd.dvd.mul_left hx a

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result.

Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.

Simplify using the standard rewrite rules. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_represent_mod_of_basis {R ι : Type*} [CommRing R] [Fintype ι]
    (b : Module.Basis ι ℤ R) (N : ℕ) (hN : 0 < N) (T : R →+ ℤ)
    (hT : ∀ c : R, (∀ d : R, (N : ℤ) ∣ T (c * d)) → ∃ y : R, c = N • y) (f : R →+ ℤ) :
    ∃ x : R, ∀ c : R, (N : ℤ) ∣ f c - T (c * x) := by
  classical
  haveI : NeZero N := ⟨hN.ne'⟩
  let M : Matrix ι ι (ZMod N) := fun k l => ((T (b k * b l) : ℤ) : ZMod N)
  have key : ∀ (w : ι → ℤ) (k : ι),
      ((T (b k * ∑ l, w l • b l) : ℤ) : ZMod N) = M.mulVec (fun l => (w l : ZMod N)) k := by
    intro w k
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_zsmul, smul_eq_mul, Matrix.mulVec,
      dotProduct, M]
    push_cast
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have lift : ∀ v : ι → ZMod N, ∃ w : ι → ℤ, (fun l => (w l : ZMod N)) = v := fun v =>
    ⟨fun l => (ZMod.intCast_surjective (v l)).choose,
      funext fun l => (ZMod.intCast_surjective (v l)).choose_spec⟩
  have hinj : Function.Injective M.mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    obtain ⟨w, rfl⟩ := lift v
    have h1 : ∀ d : R, (N : ℤ) ∣ T ((∑ l, w l • b l) * d) := by
      intro d
      refine dvd_functional_of_basis b N
        (T.comp (AddMonoidHom.mulLeft (∑ l, w l • b l))) (fun k => ?_) d
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have := key w k
      rw [mul_comm] at this
      change ((T ((∑ l, w l • b l) * b k) : ℤ) : ZMod N) = 0
      rw [this]
      exact congrFun hv k
    obtain ⟨y, hy⟩ := hT _ h1
    funext l
    have h2 : w l = N * b.repr y l := by
      have := congrArg (fun z => b.repr z l) hy
      simp only [map_sum, map_zsmul, map_nsmul, Module.Basis.repr_self] at this
      simpa [Finsupp.single_apply] using this
    simp [h2]
  have hsurj : Function.Surjective M.mulVecLin := Finite.surjective_of_injective hinj
  obtain ⟨v, hv⟩ := hsurj (fun k => ((f (b k) : ℤ) : ZMod N))
  obtain ⟨w, rfl⟩ := lift v
  refine ⟨∑ l, w l • b l, fun c => ?_⟩
  refine dvd_functional_of_basis b N
    (f - T.comp (AddMonoidHom.mulRight (∑ l, w l • b l))) (fun k => ?_) c
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  change ((f (b k) - T (b k * ∑ l, w l • b l) : ℤ) : ZMod N) = 0
  rw [Int.cast_sub, key, sub_eq_zero]
  exact (congrFun hv k).symm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_represent_mod_ringOfIntegers {E : Type} [Field E] [NumberField E] (N : ℕ)
    (hN : 0 < N) (T : 𝓞 E →+ ℤ)
    (hT : ∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T (c * d)) → ∃ b : 𝓞 E, c = N • b)
    (f : 𝓞 E →+ ℤ) : ∃ x : 𝓞 E, ∀ c : 𝓞 E, (N : ℤ) ∣ f c - T (c * x) :=
  exists_represent_mod_of_basis (RingOfIntegers.basis E) N hN T hT f

end GlobalTheory
