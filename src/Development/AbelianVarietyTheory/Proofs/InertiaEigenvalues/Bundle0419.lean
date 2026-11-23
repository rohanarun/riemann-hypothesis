module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0385
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
public import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0397
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniversalSelmerCocycleBaseChange
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.UnivCocycle

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

theorem ev_mk {B Y : Type} [CommRing B] [AddCommGroup Y] [Module B Y] {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) B) (x : Fin a → Y)
    (hx : matAct Ψ x = 0) (v : Fin a → B) : ev Ψ x hx (Submodule.Quotient.mk v) = ∑ j, v j • x j := by
  simp [ev, Fintype.linearCombination_apply]

theorem univ_ker {B : Type} [CommRing B] {a : ℕ} (Ψ : Matrix (Fin a) (Fin a) B) :
    matAct Ψ (fun j => (Submodule.Quotient.mk (Pi.single j 1) : (Fin a → B) ⧸ what₂ Ψ)) = 0 := by
  funext c
  have h : (∑ j, Ψ c j • (Pi.single j 1 : Fin a → B)) = Ψ c := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : (Submodule.Quotient.mk (Ψ c) : (Fin a → B) ⧸ what₂ Ψ) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span ⟨c, rfl⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h, ← Submodule.mkQ_apply, map_sum] at h2
  simpa [matAct] using h2

theorem tors {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (i : X.Tw)
    {B : Type} [CommRing B] [Algebra (X.O0 i) B] (hK : Kills i B) (Y : Type) [AddCommGroup Y] [Module B Y] (b : Y) :
    ∃ n : ℕ, (X.l i ^ n) • b = 0 := by
  refine ⟨nu X i + 1, ?_⟩
  have h := hK ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i))
    (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (GlobalTheory.ResSel.SmallSub.l_mem X i))
  rw [map_mul, map_pow, map_natCast] at h
  rw [← Nat.cast_smul_eq_nsmul B, Nat.cast_pow, pow_succ, h, zero_smul]

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
  obtain ⟨hrep, hsel⟩ := _root_.GlobalTheory.NewPrime.ScalarChange.selC_transfer D N X bkP i s _ B φ (delInv i M d) κ hκ Y hY
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
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabOfReps
section
noncomputable section

open Formalism.IndefR.Bridge

namespace GlobalTheory.ClassTrace

variable {O Γ Hf P : Type} [CommRing O] [Group Γ] [Group Hf] [AddCommGroup P] [Module O P]
  (ι : Γ →* Hf) (J : Subgroup Hf) (lam : J →* Oˣ) (ρ : Representation O Γ P)


open Classical in
def lamExt (x : Hf) : O := if hx : x ∈ J then (lam ⟨x, hx⟩ : O) else 0

theorem lamExt_coe (k : J) : lamExt J lam (k : Hf) = (lam k : O) := by
  simp [lamExt]

theorem lamExt_of_not_mem {x : Hf} (hx : x ∉ J) : lamExt J lam x = 0 := by
  simp [lamExt, hx]

theorem lamExt_mul (x : Hf) (k : J) : lamExt J lam (x * k) = lamExt J lam x * (lam k : O) := by
  by_cases hx : x ∈ J
  · have hxk : x * (k : Hf) ∈ J := J.mul_mem hx k.2
    unfold lamExt
    rw [dite_eq_left hxk, dite_eq_left hx, ← Units.val_mul, ← map_mul]
    rfl
  · have hxk : x * (k : Hf) ∉ J := fun hm => hx (by simpa using J.mul_mem hm (J.inv_mem k.2))
    rw [lamExt_of_not_mem J lam hx, lamExt_of_not_mem J lam hxk, zero_mul]

def traceForm (h : Hf) (p : P) (x : Hf) : P := ∑ᶠ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p

def link (h x : Hf) : Set Γ := {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}

theorem mem_link_iff {h x : Hf} {γ : Γ} : γ ∈ link ι J h x ↔ ∃ k : J, x = ι γ * h * k := by
  constructor
  · intro hγ
    refine ⟨⟨h⁻¹ * (ι γ)⁻¹ * x, hγ⟩, ?_⟩
    show x = ι γ * h * (h⁻¹ * (ι γ)⁻¹ * x)
    group
  · rintro ⟨k, rfl⟩
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    rw [show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) = (k : Hf) by group]
    exact k.2

def linkEquiv {h x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) : stab ι J x ≃ link ι J h x where
  toFun δ := ⟨δ * γ₀, by
    have h1 := J.mul_mem h0 (J.inv_mem ((mem_stab ι).1 δ.2))
    simpa [link, mul_assoc] using h1⟩
  invFun γ := ⟨γ * γ₀⁻¹, by
    have h1 := J.mul_mem (J.inv_mem γ.2) h0
    rw [mem_stab]
    simpa [link, mul_assoc] using h1⟩
  left_inv δ := by simp
  right_inv γ := by simp

theorem link_finite (hfin : ∀ x, Finite (stab ι J x)) (h x : Hf) : (link ι J h x).Finite := by
  rcases (link ι J h x).eq_empty_or_nonempty with he | ⟨γ₀, h0⟩
  · rw [he]
    exact Set.finite_empty
  · have := hfin x
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (linkEquiv ι J h0))

theorem support_subset (h : Hf) (p : P) (x : Hf) :
    (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) ⊆ link ι J h x := by
  intro γ hγ
  rw [Function.mem_support] at hγ
  by_contra hn
  have hn' : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hn
  exact hγ (by rw [lamExt_of_not_mem J lam hn', zero_smul])

theorem traceForm_eq_zero (h : Hf) (p : P) {x : Hf} (hx : ¬ ∃ (γ : Γ) (k : J), x = ι γ * h * k) :
    traceForm ι J lam ρ h p x = 0 := by
  unfold traceForm
  have hz : ∀ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p = 0 := by
    intro γ
    have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := fun hm =>
      hx ⟨γ, (mem_link_iff ι J (h := h) (x := x) (γ := γ)).1 hm⟩
    rw [lamExt_of_not_mem J lam hn, zero_smul]
  simp only [hz, finsum_zero]

theorem traceForm_law (hfin : ∀ x, Finite (stab ι J x)) (h : Hf) (p : P) (γ₀ : Γ) (x : Hf) (k : J) :
    traceForm ι J lam ρ h p (ι γ₀ * x * k) = (lam k : O) • ρ γ₀ (traceForm ι J lam ρ h p x) := by
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    (link_finite ι J hfin h x).subset (support_subset ι J lam ρ h p x)
  unfold traceForm
  conv_rhs => rw [← LinearMap.smul_apply]
  rw [map_finsum _ hf, ← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft]
  have e : h⁻¹ * (ι (γ₀ * γ))⁻¹ * (ι γ₀ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
    rw [map_mul]
    group
  rw [e, lamExt_mul, map_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

variable {C W : Type} [Field C] [AddCommGroup W] [Module C W] {e : O →+* C}

def classSum (θ : Hf → P →ₛₗ[e] W) {I : Type} [Fintype I] (y : I → Hf) (f : Hf → P) : W :=
  ∑ i, (Nat.card (stab ι J (y i)) : C)⁻¹ • θ (y i) (f (y i))

def DualLaw (θ : Hf → P →ₛₗ[e] W) : Prop :=
  ∀ (γ : Γ) (h : Hf) (k : J) (p : P), e (lam k) • θ (ι γ * h * k) (ρ γ p) = θ h p

theorem kernel_traceForm (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W} (hθ : DualLaw ι J lam ρ θ)
    (h : Hf) (p : P) {x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) :
    θ x (traceForm ι J lam ρ h p x) = (Nat.card (stab ι J x) : C) • θ h p := by
  classical
  have hL := link_finite ι J hfin h x
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    hL.subset (support_subset ι J lam ρ h p x)
  have hterm : ∀ γ : Γ, θ x (lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) =
      if γ ∈ link ι J h x then θ h p else 0 := by
    intro γ
    split_ifs with hγ
    · obtain ⟨k, hk⟩ := (mem_link_iff ι J).1 hγ
      have hk' : h⁻¹ * (ι γ)⁻¹ * x = (k : Hf) := by
        rw [hk]
        group
      rw [hk', lamExt_coe, map_smulₛₗ, ← hθ γ h k p, ← hk]
    · have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hγ
      rw [lamExt_of_not_mem J lam hn, zero_smul, map_zero]
  have hsub : Function.support (fun γ : Γ => if γ ∈ link ι J h x then θ h p else 0) ⊆
      (hL.toFinset : Set Γ) := by
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    exact hγ (if_neg hn)
  have hc : hL.toFinset.card = Nat.card (stab ι J x) := by
    rw [Nat.card_congr (linkEquiv ι J h0), Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hL]
  unfold traceForm
  rw [map_finsum (θ x) hf]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset _ hsub,
    Finset.sum_congr rfl (fun γ hγ => if_pos ((Set.Finite.mem_toFinset hL).1 hγ)),
    Finset.sum_const, hc, Nat.cast_smul_eq_nsmul]

theorem classSum_traceForm [CharZero C] (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W}
    (hθ : DualLaw ι J lam ρ θ) {I : Type} [Fintype I] {y : I → Hf} (hy : IsReps ι J y) (h : Hf) (p : P) :
    classSum ι J θ y (traceForm ι J lam ρ h p) = θ h p := by
  obtain ⟨i₀, ⟨γ, k, hh⟩, huniq⟩ := hy h
  unfold classSum
  rw [Finset.sum_eq_single i₀]
  · have h0 : γ⁻¹ ∈ link ι J h (y i₀) := by
      rw [mem_link_iff]
      refine ⟨k⁻¹, ?_⟩
      rw [hh]
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [kernel_traceForm ι J lam ρ hfin hθ h p h0]
    have := hfin (y i₀)
    have hne : (Nat.card (stab ι J (y i₀)) : C) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact inv_smul_smul₀ hne _
  · intro i _ hi
    have hx : ¬ ∃ (γ' : Γ) (k' : J), y i = ι γ' * h * k' := by
      rintro ⟨γ', k', hy'⟩
      apply hi
      apply huniq
      refine ⟨γ'⁻¹, k'⁻¹, ?_⟩
      rw [hy']
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [traceForm_eq_zero ι J lam ρ h p hx, map_zero, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

theorem finite_stab_of_reps {I : Type} {y : I → Hf} (hy : IsReps ι J y) (hfin : ∀ i, Finite (stab ι J (y i)))
    (x : Hf) : Finite (stab ι J x) := by
  obtain ⟨i, ⟨γ, k, hx⟩, -⟩ := hy x
  subst hx
  have := hfin i
  refine Finite.of_injective (β := stab ι J (y i)) (fun δ => ⟨γ⁻¹ * δ * γ, ?_⟩) ?_
  · rw [mem_stab]
    have hδ := (mem_stab ι).1 δ.2
    have e : (y i)⁻¹ * ι (γ⁻¹ * δ * γ) * y i =
        (k : Hf) * ((ι γ * y i * k)⁻¹ * ι δ * (ι γ * y i * k)) * (k : Hf)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact J.mul_mem (J.mul_mem k.2 hδ) (J.inv_mem k.2)
  · intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this

end GlobalTheory.ClassTrace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdRAndFilZeroOfJumpMultiset
section
namespace GlobalTheory.JumpDims

open Module
open scoped TensorProduct

section Linear

variable {L U : Type} [Field L] [AddCommGroup U] [Module L U]

theorem exists_le_of_exh (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hexh : ∀ x, ∃ a, x ∈ F a) : ∃ a, D ≤ F a := by
  obtain ⟨S, hS⟩ : D.FG := Module.Finite.iff_fg.mp inferInstance
  choose n hn using hexh
  obtain ⟨a, ha⟩ := (S.image n).bddBelow
  refine ⟨a, ?_⟩
  rw [← hS, Submodule.span_le]
  intro x hx
  exact hanti (ha (Finset.mem_coe.mpr (Finset.mem_image_of_mem n hx))) (hn x)

theorem exists_inf_eq_bot_of_sep (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0) : ∃ a, D ⊓ F a = ⊥ := by
  have hfin : ∀ a, FiniteDimensional L ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le inf_le_left
  let a : ℤ := Function.argmin (fun a : ℤ => finrank L ↥(D ⊓ F a))
  have ha : ∀ b, finrank L ↥(D ⊓ F a) ≤ finrank L ↥(D ⊓ F b) := fun b =>
    Function.argmin_le (fun a : ℤ => finrank L ↥(D ⊓ F a)) b
  refine ⟨a, eq_bot_iff.mpr fun x hx => ?_⟩
  rw [Submodule.mem_bot]
  refine hsep x fun b => ?_
  rcases le_total a b with h | h
  · have : D ⊓ F b = D ⊓ F a :=
      Submodule.eq_of_le_of_finrank_le (inf_le_inf_left D (hanti h)) (ha b)
    exact (this ▸ hx : x ∈ D ⊓ F b).2
  · exact hanti h hx.2

theorem card_filter_succ (M : Multiset ℤ) (a : ℤ) :
    Multiset.card (M.filter (a ≤ ·)) = Multiset.card (M.filter (a + 1 ≤ ·)) + M.count a := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons b M ih =>
    rw [Multiset.filter_cons, Multiset.filter_cons, Multiset.count_cons, Multiset.card_add,
      Multiset.card_add, ih]
    split_ifs <;> simp <;> omega

theorem finrank_of_mult (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hexh : ∀ x, ∃ a, x ∈ F a) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0)
    (M : Multiset ℤ)
    (hM : ∀ a, (finrank L ↥(D ⊓ F a) : ℤ) - finrank L ↥(D ⊓ F (a + 1)) = (M.count a : ℤ)) :
    finrank L D = Multiset.card M ∧
      ∀ a, finrank L ↥(D ⊓ F a) = Multiset.card (M.filter (a ≤ ·)) := by
  let g : ℤ → ℤ := fun a => (finrank L ↥(D ⊓ F a) : ℤ) - Multiset.card (M.filter (a ≤ ·))
  have hstep : ∀ a, g (a + 1) = g a := fun a => by
    have h1 := hM a
    have h2 := card_filter_succ M a
    simp only [g]
    omega
  have hconst : ∀ a, g a = g 0 := fun a => by
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
    | pred n ih => rw [← ih, ← hstep]; congr 1; ring
  obtain ⟨hi, hhi⟩ := exists_inf_eq_bot_of_sep D F hanti hsep
  obtain ⟨lo, hlo⟩ := exists_le_of_exh D F hanti hexh
  obtain ⟨u, hu⟩ := M.toFinset.bddAbove
  obtain ⟨l, hl⟩ := M.toFinset.bddBelow
  have hu' : ∀ x ∈ M, x ≤ u := fun x hx => hu (by simpa using hx)
  have hl' : ∀ x ∈ M, l ≤ x := fun x hx => hl (by simpa using hx)
  have h0 : g (max hi (u + 1)) = 0 := by
    have e1 : D ⊓ F (max hi (u + 1)) = ⊥ :=
      eq_bot_iff.mpr (hhi ▸ inf_le_inf_left D (hanti (le_max_left _ _)))
    have e2 : M.filter (max hi (u + 1) ≤ ·) = 0 :=
      Multiset.filter_eq_nil.mpr fun x hx h => by
        have := hu' x hx
        have := le_max_right hi (u + 1)
        omega
    show (finrank L ↥(D ⊓ F (max hi (u + 1))) : ℤ) - Multiset.card (M.filter (max hi (u + 1) ≤ ·)) = 0
    rw [e1, e2]
    simp
  have hall : ∀ a, finrank L ↥(D ⊓ F a) = Multiset.card (M.filter (a ≤ ·)) := fun a => by
    have : g a = 0 := by rw [hconst a, ← hconst (max hi (u + 1)), h0]
    simp only [g] at this
    omega
  refine ⟨?_, hall⟩
  have e1 : D ⊓ F (min lo l) = D := inf_eq_left.mpr (hlo.trans (hanti (min_le_left _ _)))
  have e2 : M.filter (min lo l ≤ ·) = M :=
    Multiset.filter_eq_self.mpr fun x hx => (min_le_right _ _).trans (hl' x hx)
  have := hall (min lo l)
  rwa [e1, e2] at this

end Linear

open GlobalTheory.TripleGal _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem finite_of_isdR {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (P : LocPrime l) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (h : Bw.IsdRW P r) :
    FiniteDimensional ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := by
  set_option synthInstance.maxHeartbeats 200000 in
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI : Subsingleton (Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hz : ∀ z : (Fin 0 → ↥Bw.LL.1) ⊗[ℚ_[l]] P.R.BdR, z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [hz x.1, hz y.1]
    haveI : Finite (Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := Finite.of_subsingleton
    exact Module.Finite.of_finite
  · haveI := (P.PD Bw.Kw).finK
    haveI : Module.Free ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_pos (by rw [h]; exact Nat.mul_pos Module.finrank_pos hm)

theorem dims_of_mult : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv) (M : Multiset ℤ), HodgeL bkP i s → (∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = (M.count a : ℤ)) → dimD bkP i v hv (Tgl i s) τ = Multiset.card M ∧ dimFil0 bkP i v hv (Tgl i s) τ = Multiset.card (M.filter (0 ≤ ·)) := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro D bkP i s v hv τ M hH hM
  have hdR := (hH v hv (Tgl i s) (Or.inr rfl)).1
  haveI := finite_of_isdR _ _ _ hdR
  haveI : FiniteDimensional _ ↥(Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ) :=
    Submodule.finiteDimensional_of_le (S₂ := Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)))
      inf_le_left
  have key := finrank_of_mult (Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ)
    (Formalism.WeaklyAdmissibleFiltrations.FilV (PDv bkP i v hv)) (GlobalTheory.DRFil.FilV_antitone _) (GlobalTheory.DRFil.exists_mem_FilV _)
    (GlobalTheory.DRFil.eq_zero_of_forall_mem_FilV _) M hM
  exact ⟨key.1, key.2 0⟩

end GlobalTheory.JumpDims
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdREOfIsCrys
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.CrysDdR

theorem finrank_DdRE_of_isCrys : ∀ D : D7, ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l), (∃ s, Good K s LL) → ∀ T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys ((D.loc l).PD K) T.ρ → ∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(DdRE ((D.loc l).PD K) T.ρ τ) = finrank ↥LL.1 T.V := by
  intro D l _ K LL _ T hc τ
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ hc).1
  exact ((GlobalTheory.Per.Components.components_finrank l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ).1 τ).2.2 hdr

end GlobalTheory.CrysDdR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankFiniteLeExponentialCocyclesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.HyodoDef GlobalTheory.Pst TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_finite_le_exponential_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → finrank ℚ_[l] ↥(finiteCocycles (P.PD K) ρ) ≤ finrank ℚ_[l] ↥(crystallineCocycles (P.PD K) ρ) + finrank ℚ_[l] ↥(Dcris (P.PD K) ρ ⊓ LinearMap.ker (φVB (P.PD K) (LL := ℚ_[l]) (V := V) - LinearMap.id)) := by
  first | exact @GlobalTheory.HyodoFE.finrank_finite_le_exponential_add | exact GlobalTheory.HyodoFE.finrank_finite_le_exponential_add | (intros; apply GlobalTheory.HyodoFE.finrank_finite_le_exponential_add <;> assumption)
end

