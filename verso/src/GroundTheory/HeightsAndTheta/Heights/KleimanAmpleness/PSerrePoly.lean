import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsSerrePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u

/- English proof (translation)
Introduce `S _ _ N`. Take `⟨hinj, hpiece, ι, hι, hres, hmk, hdeg⟩` from `hL S N`. Take `⟨hfin, hvan, hconst⟩` from `hC S N`. Establish `hφ : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N (Poly S N) I.1), ι J (locResS I J h m) = Cech.idRes S (Laurent S N) Finset.univ I J h (ι I m)` using `fun I J h m => hres I J h m`. Establish `hd : ∀ (c : ℤ) (I : StdCell N) (m : LocMod S N (Poly S N) I.1), m ∈ degLoc (polyGraded S N) c I → ι I m ∈ laurentDeg S N c I` using `fun c I m hm => by`.

Rewrite using `[← hdeg c I]`. Conclude with `Submodule.mem_map_of_mem hm`. Establish `hb : ∀ (i : ℕ) (c : ℤ), Function.Bijective (Cech.mapHdeg (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ (hd c) i)` using `fun i c => hT (N + 1) Finset.univ S _ _ _ _ (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ (hd c) hι (hdeg c) i`. Set `E : ∀ (i : ℕ) (c : ℤ), cohom (polyGraded S N) i c ≃ₗ[S] laurentCohom S N i c` to `fun i c => LinearEquiv.ofBijective _ (hb i c)`. Use `⟨fun i c => Module.Finite.equiv (E i c).symm, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Use `hvan c hc i hi` as an intermediate fact. Conclude with `(E i c).toEquiv.subsingleton`. Introduce `m m' hmm`. Establish `h0 : (constCochain (S` using `S) (N := N) (M := Poly S N) (m : Poly S N)) = constCochain (S := S) (N := N) (M := Poly S N) (m' : Poly S N) := by`. Establish `hmem` using `(Submodule.Quotient.eq _).mp hmm`.

Express the relevant statement in the definitionally equal form `_ ∈ (⊥ : Submodule S _).comap _ at hmem`. Rewrite `hmem` using `[Submodule.mem_comap, Submodule.mem_bot]`. Conclude with `sub_eq_zero.mp hmem`. Set `I0 : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0` to `⟨⟨{0}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩`. Establish `h1` using `congrArg (ι I0.1) (congrFun h0 I0)`.

Express the relevant statement in the definitionally equal form `ι I0.1 (locMk (Poly S N) I0.1.1 m) = ι I0.1 (locMk (Poly S N) I0.1.1 m') at h1`. Rewrite `h1` using `[hmk, hmk]`. Conclude with `Subtype.ext (hinj h1)`. Introduce `y`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Establish `hw : (Cech.mapC ι 0 (z : Cech.Cochain (locSys S N (Poly S N)) 0)) ∈ Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c) (Cech.idRes S (Laurent S N) Finset.univ) 0`. Use `Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, fun I _ => ?_⟩` and prove the remaining obligations. Rewrite using `[← Cech.mapC_d ι hφ, LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).1, map_zero]`. Conclude with `hd c I.1 _ ((Submodule.mem_inf.mp z.2).2 I (Set.mem_univ _))`. Take `⟨f, hf, hzf⟩` from `hconst c hc _ hw`.

Rewrite `hf` using `[← hpiece c]`. Take `⟨m, hm, rfl⟩` from `hf`. Use `⟨⟨m, hm⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `I`. Apply `hι I.1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `ι I.1 (locMk (Poly S N) I.1.1 m) = _`. Rewrite using `[hmk]`.

Conclude with `(hzf I).symm`.
-/
theorem SerrePoly.proof (hL : SerrePoly.Laurent.Statement.{u}) (hT : Cech.Transport.Statement.{u, u, u})
    (hC : SerrePoly.LaurentCohom.Statement.{u}) : SerrePoly.Statement.{u} := by
  intro S _ _ N
  obtain ⟨hinj, hpiece, ι, hι, hres, hmk, hdeg⟩ := hL S N
  obtain ⟨hfin, hvan, hconst⟩ := hC S N
  have hφ : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N (Poly S N) I.1),
      ι J (locResS I J h m) = Cech.idRes S (Laurent S N) Finset.univ I J h (ι I m) :=
    fun I J h m => hres I J h m
  have hd : ∀ (c : ℤ) (I : StdCell N) (m : LocMod S N (Poly S N) I.1),
      m ∈ degLoc (polyGraded S N) c I → ι I m ∈ laurentDeg S N c I := fun c I m hm => by
    rw [← hdeg c I]; exact Submodule.mem_map_of_mem hm
  have hb : ∀ (i : ℕ) (c : ℤ), Function.Bijective
      (Cech.mapHdeg (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ (hd c) i) :=
    fun i c => hT (N + 1) Finset.univ S _ _ _ _ (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ
      (hd c) hι (hdeg c) i
  let E : ∀ (i : ℕ) (c : ℤ), cohom (polyGraded S N) i c ≃ₗ[S] laurentCohom S N i c :=
    fun i c => LinearEquiv.ofBijective _ (hb i c)
  refine ⟨fun i c => Module.Finite.equiv (E i c).symm, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · have := hvan c hc i hi
    exact (E i c).toEquiv.subsingleton
  ·
    intro m m' hmm
    have h0 : (constCochain (S := S) (N := N) (M := Poly S N) (m : Poly S N)) =
        constCochain (S := S) (N := N) (M := Poly S N) (m' : Poly S N) := by
      have hmem := (Submodule.Quotient.eq _).mp hmm
      change _ ∈ (⊥ : Submodule S _).comap _ at hmem
      rw [Submodule.mem_comap, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    let I0 : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{0}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    have h1 := congrArg (ι I0.1) (congrFun h0 I0)
    change ι I0.1 (locMk (Poly S N) I0.1.1 m) = ι I0.1 (locMk (Poly S N) I0.1.1 m') at h1
    rw [hmk, hmk] at h1
    exact Subtype.ext (hinj h1)
  ·
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hw : (Cech.mapC ι 0 (z : Cech.Cochain (locSys S N (Poly S N)) 0)) ∈
        Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
          (Cech.idRes S (Laurent S N) Finset.univ) 0 := by
      refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, fun I _ => ?_⟩
      · rw [← Cech.mapC_d ι hφ, LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).1, map_zero]
      · exact hd c I.1 _ ((Submodule.mem_inf.mp z.2).2 I (Set.mem_univ _))
    obtain ⟨f, hf, hzf⟩ := hconst c hc _ hw
    rw [← hpiece c] at hf
    obtain ⟨m, hm, rfl⟩ := hf
    refine ⟨⟨m, hm⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext I
    apply hι I.1
    change ι I.1 (locMk (Poly S N) I.1.1 m) = _
    rw [hmk]
    exact (hzf I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
