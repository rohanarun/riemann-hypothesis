module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0325
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsSmulOfMapResidueEqZero
public import Formalism.SubspaceCounting.ChoiceOfTopsRefined
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightWittLeviLePowOfBoundedUnipo
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmoothWeilOrbitRealPassesToHeisenbergDerivatives
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbitReal

theorem orbit_heis_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ τ : ∀ w : InfinitePlace F, EmbOver E w, (∀ w, IsCartan (X.J.map (τ w).1) (X.θ w)) →
        (∀ w, IsCartan (Complex.I • W.J.map (τ w).1) (W.θ w)) →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f p.2) →
          (∃ f' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f x) (f' x) 0) →
          ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ →
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) ∧ ∃ f₁' ∈ M.Pol ψ τ, ∀ x, HasDerivAt (fun t => T t f₁ x) (f₁' x) 0 := by
  intro F E _ _ _ _ _ σ _hCM n d X W M ψ χX χW om hψ _ _ _ _ _ _ _ _ hW τ _ _ γ hγ T hTa u hu f hf hsm hder f₁ hf₁
  obtain ⟨f', hf'P, hf'd⟩ := hder
  have hstab : ∀ v : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) v → ∀ g ∈ M.Pol ψ τ,
      ∃ g₁ ∈ M.Pol ψ τ, ∀ y, g₁ y = dOp (archCo M.co v).1 (archCo M.co v).2 g y := by
    intro v hv g hg
    obtain ⟨D, hD⟩ := _root_.GlobalTheory.HeisDer.derEx F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J)
      M.co hψ
    have h0 : ∀ t, M.heisLine ψ v t 0 = 0 := fun t => by
      funext x
      simp [Model.heisLine, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
    have hA : ActsD (evI F) (M.heisLine ψ v) g (D v g) :=
      (GlobalTheory.RealLift.actsLaws F _ g (D v g) (D v g)).1 _ h0 (hD v hv g).1
    refine ⟨D v g, Submodule.mem_sInf.2 fun N hN => hN.2 v hv g (Submodule.mem_sInf.1 hg N hN) _ hA, fun y => ?_⟩
    rw [(hD v hv g).2 y]
    rfl
  have hrel : ∀ t y, T t f₁ y = dOp (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1
      (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2 (T t f) y := fun t =>
    GlobalTheory.T.weil_operator_right_intertwines_heisenberg_derivative M ψ χX χW om hψ hW (γ (Multiplicative.ofAdd t)) (T t) (hTa t) u hu f f₁ hf₁
  obtain ⟨hφ, u', hu', hφd⟩ := GlobalTheory.T.heisenberg_orbit_coefficient_smooth M γ hγ u hu
  have hfun : (fun p : ℝ × (Fin n × Fin d → mixedEmbedding.mixedSpace F) => T p.1 f₁ p.2) =
      fun p => dOp (archCo M.co (u * (mat (γ (Multiplicative.ofAdd p.1)))ᵀ)).1
        (archCo M.co (u * (mat (γ (Multiplicative.ofAdd p.1)))ᵀ)).2 (T p.1 f) p.2 :=
    funext fun p => hrel p.1 p.2
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GlobalTheory.HeisOrbit.dOp_contDiff_family (fun t => T t f) (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1)
      (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2) hsm hφ.fst hφ.snd
  have hT0 : T 0 f = f := by
    have h1 : om (1, γ (Multiplicative.ofAdd 0)) = 1 := by
      rw [ofAdd_zero, map_one]
      exact map_one om
    have hA : Acts (evI F) (om (1, γ (Multiplicative.ofAdd 0))) f f := by
      rw [h1]
      intro r _
      rfl
    exact (GlobalTheory.RealLift.actsLaws F _ f (T 0 f) f).2.2.2.1 _ (hTa 0 f) hA
  have hφ0 : archCo M.co (u * (mat (γ (Multiplicative.ofAdd (0 : ℝ))))ᵀ) = archCo M.co u := by
    rw [ofAdd_zero, map_one]
    simp [mat]
  obtain ⟨g₁, hg₁P, hg₁⟩ := hstab u hu f' hf'P
  obtain ⟨g₂, hg₂P, hg₂⟩ := hstab u' hu' f hf
  refine ⟨g₁ + g₂, add_mem hg₁P hg₂P, fun x => ?_⟩
  have hP := (hasFDerivAt_fst (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have hQ := (hasFDerivAt_snd (𝕜 := ℝ)).comp_hasDerivAt (0 : ℝ) hφd
  have h4 := GlobalTheory.HeisOrbit.DOpDeriv.dOp_hasDerivAt (fun t => T t f) (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).1)
    (fun t => (archCo M.co (u * (mat (γ (Multiplicative.ofAdd t)))ᵀ)).2) f' _ _ hsm hf'd hP hQ x
  simp only [hφ0, hT0] at h4
  rw [SchwartzMap.add_apply, hg₁, hg₂]
  exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => hrel t x)

end GlobalTheory.HeisOrbitReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceHeckeDoubleCosetCardGaussBinom
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.SplitCosetCount

section Grp

open Classical

variable {G : Type} [Group G]

theorem card_le_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card ≤ B.card := by
  classical
  have f : ∀ a ∈ A, ∃ b, b ∈ B ∧ b⁻¹ * a ∈ J := fun a ha => (hB.2 a (hA.1 a ha)).exists
  choose! φ hφB hφJ using f
  refine Finset.card_le_card_of_injOn φ (fun a ha => hφB a ha) ?_
  intro a₁ ha₁ a₂ ha₂ he
  have h1 : a₁⁻¹ * a₂ ∈ J := by
    have h := J.mul_mem (J.inv_mem (hφJ a₁ ha₁)) (hφJ a₂ ha₂)
    have e : ((φ a₁)⁻¹ * a₁)⁻¹ * ((φ a₂)⁻¹ * a₂) = a₁⁻¹ * a₂ := by rw [he]; group
    rwa [e] at h
  exact (hA.2 a₂ (hA.1 a₂ ha₂)).unique ⟨ha₁, h1⟩ ⟨ha₂, by simp⟩

theorem card_eq_of_isDC {J : Subgroup G} {x : G} {A B : Finset G} (hA : Bridge.IsDC J x A)
    (hB : Bridge.IsDC J x B) : A.card = B.card :=
  le_antisymm (card_le_of_isDC hA hB) (card_le_of_isDC hB hA)

variable {H : Type} [Group H] {ρ : G →* H} {S : G → Prop} {K : Set G} {K' : Subgroup H}

theorem lift_isReps (hm : ∀ x y, S x → S y → S (x * y)) (hi : ∀ x, S x → S x⁻¹)
    (hinj : ∀ x y, S x → S y → ρ x = ρ y → x = y) (hK : ∀ g, S g → (g ∈ K ↔ ρ g ∈ K'))
    {g : G} (hg : S g) {R₀ : Finset H} (hR : Formalism.IndefR.Fin.HCount.IsReps K' (ρ g) R₀)
    (ψ : H → G) (hψs : ∀ a, S (ψ a)) (hψ : ∀ a, ρ (ψ a) = a) :
    (∀ γ ∈ R₀.image ψ, ∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ {k | k ∈ K ∧ S k}, ∃ k₂ ∈ {k | k ∈ K ∧ S k}, x = k₁ * g * k₂) →
        ∃! γ, γ ∈ R₀.image ψ ∧ γ⁻¹ * x ∈ {k | k ∈ K ∧ S k} := by
  classical
  have hex : ∀ a, ∃ g, S g ∧ ρ g = a := fun a => ⟨ψ a, hψs a, hψ a⟩
  refine ⟨fun γ hγ => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hγ
    exact GlobalTheory.SplitPlace.lift_dc hm hex hinj hK hg (hψs a) (by rw [hψ]; exact hR.1 a ha)
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have hx := hm _ _ (hm _ _ hk₁.2 hg) hk₂.2
    have key : ∀ a, (ψ a)⁻¹ * (k₁ * g * k₂) ∈ {k | k ∈ K ∧ S k} ↔ a⁻¹ * ρ (k₁ * g * k₂) ∈ K' := by
      intro a
      have hs := hm _ _ (hi _ (hψs a)) hx
      have := hK _ hs
      rw [map_mul, map_inv, hψ] at this
      exact ⟨fun h => this.1 h.1, fun h => ⟨this.2 h, hs⟩⟩
    obtain ⟨a, ⟨ha, ha'⟩, hu⟩ := hR.2 (ρ (k₁ * g * k₂)) ⟨_, (hK _ hk₁.2).1 hk₁.1, _, (hK _ hk₂.2).1 hk₂.1,
      by rw [map_mul, map_mul]⟩
    refine ⟨ψ a, ⟨Finset.mem_image_of_mem _ ha, (key a).2 ha'⟩, ?_⟩
    rintro γ ⟨hγ, h⟩
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hγ
    rw [hu b ⟨hb, (key b).1 h⟩]

theorem card_image_section {R₀ : Finset H} (ψ : H → G) (hψ : ∀ a, ρ (ψ a) = a) :
    (R₀.image ψ).card = R₀.card := by
  classical
  refine Finset.card_image_of_injective _ fun a b h => ?_
  rw [← hψ a, ← hψ b, h]

end Grp

theorem gaussBinom_eq (κ : Type) [Field κ] [Fintype κ] (n k : ℕ) :
    Formalism.G0.gaussBinom (Fintype.card κ) n k = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Fintype.card κ) n k := by
  have h1 := Formalism.G0.Top.subspaceCount (F := κ) (W := Fin n → κ) k
  have h2 := GlobalTheory.GaussCount.subspaceCount κ (Fin n → κ) k
  rw [Module.finrank_fin_fun] at h1 h2
  rw [Nat.card_eq_fintype_card (α := κ)] at h2
  rw [← h1, ← h2]
  unfold Formalism.G0.countBelow
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight fun U => by simp

end GlobalTheory.SplitCosetCount

namespace GlobalTheory.SplitCosetCount

open Classical
open Formalism.IndefR.Lev GlobalTheory.HeckeParts Formalism.L2.NTheta


set_option maxHeartbeats 1000000 in
theorem card_cosets : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))), Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → k ≤ D.R.r →
    IsHeckeAt (Wc D i) P k α → Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Rc.card = GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm P.asIdeal) D.R.r k := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc hso hk hα hRc
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨e, ϖ, he, h1, h2, hαe⟩ := hα
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨v, π, s, c1, c2, c3, c4, c5⟩ := GlobalTheory.SplitCoord.exists_coord e he.1
  obtain ⟨B, hB⟩ := GlobalTheory.SplitLatBasis.exists_basis (Wc D i) e v π s he.1.1 c2 c3 c4
    (GlobalTheory.LatDual.lamHat_selfDual_and_module (Wc D i)).2
  obtain ⟨hex, hinj⟩ := GlobalTheory.SplitPlace.comp_bij (V := Wc D i) (B := B) he.1 c1 c2
  have hKc := fun g => GlobalTheory.SplitPlace.K_iff (V := Wc D i) (g := g) he.1 c2 c3 hB
  have hu := GlobalTheory.SplitPlace.isUnif he c4 c5 ϖ h1 h2
  obtain ⟨hu0, hu1⟩ := GlobalTheory.SplitPlace.unif_facts hu
  have hH := (GlobalTheory.SplitPlace.hecke_iff he.1 c1 c2 c3 c4 hB hu0 k α).1 hαe

  obtain ⟨w, hw⟩ : ∃ w, π (finPart D (incA D (ϖ : D.host.E))) = w := ⟨_, rfl⟩
  rw [hw] at hu hu0 hu1 hH
  have hirr : Irreducible (⟨w, hu1⟩ : Formalism.UG.Ov D.host.F v) :=
    Formalism.IndefR.Fin.HCount.irreducible_of_unif D.host.F v ⟨w, hu1⟩ hu
  have hv0 : Valued.v w ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
  have htype : Formalism.IndefR.Fin.HCount.IsType (Formalism.UG.Ov D.host.F v) ⟨w, hu1⟩ k
      (GlobalTheory.SplitPlace.comp (Wc D i) π B α) := by
    refine ⟨fun a b => hH.2.1 a b, fun a b => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact hH.2.2.1 a b
    · obtain ⟨d, hd⟩ : ∃ d, (GlobalTheory.SplitPlace.comp (Wc D i) π B α).1.det = d := ⟨_, rfl⟩
      have hdv' := hH.2.2.2
      rw [hd] at hdv'
      have hdv : Valued.v (d / w ^ k) = 1 := by
        rw [map_div₀, map_pow, hdv', div_self (pow_ne_zero _ hv0)]
      have hne : d / w ^ k ≠ 0 := fun h => by rw [h, map_zero] at hdv; exact zero_ne_one hdv
      have hm : d / w ^ k ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)) ≤ 1; exact le_of_eq hdv
      have hmi : (d / w ^ k)⁻¹ ∈ Formalism.UG.Ov D.host.F v := by show Valued.v ((d / w ^ k : v.adicCompletion D.host.F)⁻¹) ≤ 1; rw [map_inv₀, hdv, inv_one]
      refine ⟨⟨d / w ^ k, hm⟩, isUnit_iff_exists_inv.2 ⟨⟨_, hmi⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩, ?_⟩
      show _ = w ^ k * (d / w ^ k)
      rw [hd, mul_div_cancel₀ _ (pow_ne_zero _ hu0)]

  obtain ⟨R₀, hR₀⟩ := GlobalTheory.SplitPlace.exists_reps (Formalism.UG.Final.GLintComm D.host.F v (Wc D i).rank)
    (GlobalTheory.SplitPlace.comp (Wc D i) π B α)
  have hc0 := Formalism.IndefR.Fin.HCount.card_reps (Formalism.UG.Ov D.host.F v) hirr htype (R := R₀) hR₀
  choose ψ hψs hψ using hex
  have hl := lift_isReps (ρ := GlobalTheory.SplitPlace.comp (Wc D i) π B) (S := SuppAt e (Wc D i))
    (K := (KsphC (Wc D i) ∅ : Set (GA D (Wc D i)))) (fun _ _ => GlobalTheory.SplitPlace.suppAt_mul)
    (fun _ => GlobalTheory.SplitPlace.suppAt_inv) hinj hKc hH.1 hR₀ ψ hψs hψ
  have hdc : Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α (R₀.image ψ) := by
    refine isDC_of_splits hs levG_le_flag ((hLp α).2 hH.1) (fun a ha => ?_) hK hl.1 hl.2
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 ha
    exact (hLp _).2 (hψs b)
  let φ : D.host.E →+* v.adicCompletion D.host.F := (π.comp (finPart D)).comp (incA D)
  have hP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (φ x) < 1 := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx0 : Valued.v (φ x) ≠ 0 := by
        rw [Valuation.ne_zero_iff, map_ne_zero]
        exact fun h => hx (Subtype.ext h)
      rw [he.2 x hx, map_mul, c4]
      show ¬ Valued.v (φ (x : D.host.E)⁻¹) ≤ 1 ↔ _
      rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 hx0)]
  have hq : Fintype.card (IsLocalRing.ResidueField (Formalism.UG.Ov D.host.F v)) = Ideal.absNorm P.asIdeal := by
    rw [← Nat.card_eq_fintype_card]
    exact GlobalTheory.SplitUnif.card_residueField v φ P c5 hP
  rw [card_eq_of_isDC hRc hdc, card_image_section ψ hψ, hc0, gaussBinom_eq, hq, rank_Wc]

end GlobalTheory.SplitCosetCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTraceIsTranslSum
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {K : Type} [CommRing K]

theorem conj_pullback_map (x : Sp K ⟶ Xo.X) (g : Xo.univ.t.G ⟶ Xo.univ.t.G) :
    conj x x ((Over.pullback x).map g).left =
      (lift (fst (Over.mk x) Xo.univ.t.G) (snd (Over.mk x) Xo.univ.t.G ≫ g)).left := by
  refine gx_ext ?_ ?_
  · rw [lift_l_fst]
    exact (over_iff _).2 (pullback.lift_snd _ _ _)
  · rw [lift_l_snd, conj_apply, Category.assoc, Category.assoc, swap_inv_snd, Over.comp_left, ← swap_hom_fst,
      Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)

theorem conj_comp_left {x x' x'' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo x' ⟶ Fib Xo x'') :
    conj x x'' (f ≫ g).left = conj x x' f.left ≫ conj x' x'' g.left := by
  simp only [conj_apply, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Over.comp_left]
  simp only [Category.assoc]

theorem conj_id_pow (x : Sp K ⟶ Xo.X) (n : ℕ) :
    conj x x (𝟙 (Fib Xo x) ^ n).left = (mulT Xo.univ.t.G (Over.mk x) n).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G ^ n) = 𝟙 (Fib Xo x) ^ n := by
    have := map_pow (Over.pullback x).homMonoidHom (𝟙 Xo.univ.t.G) n
    rw [← (Over.pullback x).map_id]
    exact this
  rw [← e, conj_pullback_map, MonObj.comp_pow, Category.comp_id, mulT]

theorem conj_id_inv (x : Sp K ⟶ Xo.X) :
    conj x x (𝟙 (Fib Xo x))⁻¹.left = (negT Xo.univ.t.G (Over.mk x)).left := by
  have e : (Over.pullback x).map (𝟙 Xo.univ.t.G)⁻¹ = (𝟙 (Fib Xo x))⁻¹ := by
    rw [Functor.map_inv', CategoryTheory.Functor.map_id]
  rw [← e, conj_pullback_map, GrpObj.comp_inv, Category.comp_id, negT]
  rfl

theorem negT_comm_conj {x x' : Sp K ⟶ Xo.X} (f : Fib Xo x ⟶ Fib Xo x') [IsMonHom f] :
    (negT Xo.univ.t.G (Over.mk x)).left ≫ conj x x' f.left =
      conj x x' f.left ≫ (negT Xo.univ.t.G (Over.mk x')).left := by
  rw [← conj_id_inv, ← conj_id_inv, ← conj_comp_left, ← conj_comp_left, GrpObj.inv_comp, GrpObj.comp_inv,
    Category.id_comp, Category.comp_id]

theorem pow_eq_one_of_mem_transKer_conj {x x' : Sp K ⟶ Xo.X} {f : Fib Xo x ⟶ Fib Xo x'} {f' : Fib Xo x' ⟶ Fib Xo x}
    {n : ℕ} (h : f ≫ f' = 𝟙 _ ^ n) {c : Over.mk x ⟶ Xo.univ.t.G} (hc : c ∈ transKer Xo.univ.t.G (conj x x' f.left)) :
    c ^ n = 1 := by
  rw [← mem_transKer_mulT, mem_transKer, ← conj_id_pow, ← h, conj_comp_left, ← Category.assoc, mem_transKer.1 hc]

theorem thetaTrace_isTranslSum (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (K : Type) [Field K] (x x' : Sp K ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x')
    (f' : Fib Xo x' ⟶ Fib Xo x) (p : ℕ) (s : LB.Sec (PPx x)) (s₀ s' : LB.Sec (PPx x')) (a : K)
    (hf : IsPair (p ^ 2) f f') (hs' : ∀ i, s'.f i = scal x' a i * s₀.f i)
    (h : IsThetaTrace Xo.univ.t.G Xo.univ.t.PP (conj x x' f.left) p s s') :
    ∃ t, IsPullOf p f a s₀ t ∧ IsTranslSum p s t := by
  obtain ⟨β, s₁, t, n, U, F, hβ, hs, ht, hr, hU, hF, hsum⟩ := h
  have := hf.1
  refine ⟨t, ⟨β, s', hβ, hs', ht⟩, n, F, fun i => ?_, hsum⟩
  have hk : (U i).pt ^ (p ^ 2) = 1 := pow_eq_one_of_mem_transKer_conj hf.2.2.1 (hU i).1
  obtain ⟨α₀, α, h₁, h₂, h₃, h₄⟩ := hs
  exact ⟨_, (U i).pt, α₀, α, s₁, U i, rfl, hk, h₁, h₂, h₃, h₄,
    (hU i).symLift hβ.2.1 Xo.univ.t.sym (negT_comm_conj f) hk, hF i⟩

end GlobalTheory.HkIntegral
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslationCommutesCanonicalBaseChangeMap
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

theorem translT_comp_isCan : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} (c : Over.mk x ⟶ Xo.univ.t.G) (c₁ : Over.mk x₁ ⟶ Xo.univ.t.G), IsCan χ pm → c₁.left = spMap χ ≫ c.left → (translT Xo.univ.t.G c₁).left ≫ pm = pm ≫ (translT Xo.univ.t.G c).left := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x₁ pm c c₁ h hc
  have hw : pm ≫ (Over.mk x ⊗ Xo.univ.t.G).hom = (Over.mk x₁ ⊗ Xo.univ.t.G).hom := by
    rw [← Over.w (snd (Over.mk x) Xo.univ.t.G), ← Over.w (snd (Over.mk x₁) Xo.univ.t.G), ← Category.assoc, h.2.1]
  let P : Over.mk x₁ ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G := Over.homMk pm hw
  let Φ : Over.mk x₁ ⟶ Over.mk x := Over.homMk (spMap χ) h.1.symm
  have hPf : P ≫ fst (Over.mk x) Xo.univ.t.G = fst (Over.mk x₁) Xo.univ.t.G ≫ Φ :=
    Over.OverMorphism.ext (by simpa [P, Φ] using h.2.2)
  have hPs : P ≫ snd (Over.mk x) Xo.univ.t.G = snd (Over.mk x₁) Xo.univ.t.G :=
    Over.OverMorphism.ext (by simpa [P] using h.2.1)
  have hΦ : Φ ≫ c = c₁ := Over.OverMorphism.ext (by simpa [Φ] using hc.symm)
  have key : translT Xo.univ.t.G c₁ ≫ P = P ≫ translT Xo.univ.t.G c := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, hPf, translT, translT, lift_fst, lift_fst_assoc]
      exact hPf.symm
    · rw [Category.assoc, Category.assoc, hPs, translT, translT, lift_snd, lift_snd, translPt, translPt,
        comp_lift_assoc, reassoc_of% hPf, hPs, hΦ]
  have := congrArg CommaMorphism.left key
  simpa [P] using this

end GlobalTheory.HeckeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightComparableWittDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.HtWitt

theorem reduce (hT2 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C) (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) :
    ∃ C₁ : ℝ, ∀ n ∈ flagN d, ∀ h : GA D S₀, ∃ n' ∈ flagN d, ∃ h' : GA D S₀, height S n' ≤ C₁ ∧
      height S₀ h' ≤ 2 * quotHeight S₀ h ∧ quotHeight S₀ h' = quotHeight S₀ h ∧
      quotHeight S (n' * d.emb0 h') = quotHeight S (n * d.emb0 h) := by
  obtain ⟨C₁, hC₁⟩ := hT2 D S S₀ ρ d
  refine ⟨C₁, fun n hn h => ?_⟩
  obtain ⟨δ, hδ, hδh⟩ := exists_height_le_two_mul_quotHeight S₀ h
  have hm : d.emb0 δ * n * (d.emb0 δ)⁻¹ ∈ flagN d := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn δ
  obtain ⟨γ, hγ, hγN, hγC⟩ := hC₁ _ hm
  refine ⟨γ * (d.emb0 δ * n * (d.emb0 δ)⁻¹), mul_mem hγN hm, δ * h, hγC, hδh, quotHeight_left S₀ hδ h, ?_⟩
  have e : γ * (d.emb0 δ * n * (d.emb0 δ)⁻¹) * d.emb0 (δ * h) = (γ * d.emb0 δ) * (n * d.emb0 h) := by
    rw [map_mul]; group
  rw [e, quotHeight_left S (mul_mem hγ (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hδ))]

theorem main (hT1 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀, height S (d.emb0 g) ≤ C * height S₀ g) (hT2 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C) (hT3 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (C₀ : ℝ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, height S n ≤ C₀ → ∀ h : GA D S₀, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a) : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a := by
  intro D S S₀ ρ d
  obtain ⟨C₁, hC₁⟩ := reduce hT2 D S S₀ ρ d
  obtain ⟨C₂, hC₂⟩ := hT1 D S S₀ ρ d
  obtain ⟨C₃, a₃, hC₃⟩ := hT3 D S S₀ ρ d C₁
  have hC2 : 0 ≤ C₂ := by
    have := hC₂ 1
    rw [map_one, height_one, height_one] at this
    linarith
  refine ⟨max C₃ (C₁ * C₂ * 2) , max a₃ 1, fun n hn h => ?_⟩
  obtain ⟨n', hn', h', hn'C, hh', hq0, hq⟩ := hC₁ n hn h
  have hC1 : 0 ≤ C₁ := (height_pos S n').le.trans hn'C
  have q1 : 1 ≤ quotHeight S (n * d.emb0 h) := one_le_quotHeight S _
  have q0 : 1 ≤ quotHeight S₀ h := one_le_quotHeight S₀ _
  have hM : 0 ≤ max C₃ (C₁ * C₂ * 2) := le_max_of_le_right (by positivity)
  constructor
  · have h3 := hC₃ n' hn' hn'C h'
    rw [hq0, hq] at h3
    exact h3.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ q1 (le_max_left _ _)) (by positivity) hM)
  · have hb : quotHeight S (n' * d.emb0 h') ≤ C₁ * C₂ * 2 * quotHeight S₀ h := by
      have h1 := height_mul_le S n' (d.emb0 h')
      have h2 := hC₂ h'
      have hp : 0 ≤ height S (d.emb0 h') := (height_pos S _).le
      calc quotHeight S (n' * d.emb0 h') ≤ height S n' * height S (d.emb0 h') := (quotHeight_le_height S _).trans h1
        _ ≤ C₁ * (C₂ * height S₀ h') := mul_le_mul hn'C h2 hp hC1
        _ ≤ C₁ * (C₂ * (2 * quotHeight S₀ h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh' hC2) hC1
        _ = C₁ * C₂ * 2 * quotHeight S₀ h := by ring
    rw [hq] at hb
    refine hb.trans (mul_le_mul (le_max_right _ _) ?_ (by linarith) hM)
    calc quotHeight S₀ h = quotHeight S₀ h ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ q0 (le_max_right _ _)

end GlobalTheory.HtWitt

namespace GlobalTheory.HtWitt

theorem quotHeight_witt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a :=
  main _root_.GlobalTheory.EmbHeight.unitaryAdelicHeight_wittEmbedding_le _root_.GlobalTheory.FlagHeight.exists_rat_translate_height_le _root_.GlobalTheory.HtWittLow.quotHeight_le_of_height_le

end GlobalTheory.HtWitt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittCoreEmbeddingMulVecMemLatticeOfSplitsStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittCoreEmbedding_mulVec_mem_lattice_of_splits : ∀ {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) {L : Lat S} {L₀ : Lat S₀}, (∀ z : Fin S.rank → D.host.E, (∀ v : GlobalTheory.FinPl.Pl D, (fun i => pairA D.host.F 0 (GlobalTheory.FinPl.LatMem.indP D.host.F (· = v)) ⊗ₜ[D.host.F] z i) ∈ latV S L (· = v)) → z ∈ L) → (∀ v, MonoAt d L L₀ v) → ∀ y ∈ L₀, d.i₀ *ᵥ y ∈ L := by
  first | exact @GlobalTheory.WittCoreLat.i₀_mulVec_mem | exact GlobalTheory.WittCoreLat.i₀_mulVec_mem | (intros; apply GlobalTheory.WittCoreLat.i₀_mulVec_mem <;> assumption)
end
end

