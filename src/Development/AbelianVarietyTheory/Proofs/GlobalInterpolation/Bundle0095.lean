module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Counterexamples.PlaceInjectivity.StandardDeterminantUnits
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUnitaryCarries
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemUnitOff
public import Formalism.LocalRingCardinality.Lemmas
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeanSquareNormalizedThetaTwoTorsion

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVDetLat
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

namespace GlobalTheory.CharVal.DetFrame

theorem maxV_detLat (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (N : Submodule (𝓞 E) (Sp E n))
    (P : HeightOneSpectrum (𝓞 E)) (f : Sp E n ≃ₗ[E] Sp E n)
    (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) :
    MaxV P (detLat N) (P.valuation E ((LinearEquiv.det f : Eˣ) : E)) := by
  classical
  rw [LinearEquiv.coe_det]
  refine ⟨val_le_of_span ?_, ?_⟩
  · rintro a ⟨A, hA, rfl⟩
    let g : Sp E n →ₗ[E] Sp E n := Matrix.toLin' A
    have hg : ∀ x ∈ stdAt E n P, ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) x ∈ stdAt E n P := by
      intro x hx
      rw [← hf]
      obtain ⟨s, hs, hx⟩ := (mem_locP P _ _).1 hx
      refine (mem_locP P _ _).2 ⟨s, hs, ?_⟩
      have h1 := hA _ hx
      have h2 : A.mulVec (s • x) = s • f (((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) x) := by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
        rw [Matrix.mulVec_smul]
        rfl
      rwa [h2] at h1
    have h := GlobalTheory.Survey.StandardDeterminantUnits.val_det_le_one _ hg
    have h3 : LinearMap.det (f : Sp E n →ₗ[E] Sp E n) *
        LinearMap.det ((f.symm : Sp E n →ₗ[E] Sp E n) ∘ₗ g) = A.det := by
      rw [LinearMap.det_comp, ← mul_assoc, LinearEquiv.det_mul_det_symm, one_mul]
      exact LinearMap.det_toLin' A
    rw [← h3, map_mul]
    exact mul_le_of_le_one_right' h
  · have h1 : ∀ i : Fin n, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ s • f (Pi.single i (1 : E)) ∈ N := fun i =>
      (mem_locP P _ _).1 ((hf _).2 (le_locP P _ (by simpa using single_mem_stdLat (E := E) i 1)))
    choose s hs hs' using h1
    set t : 𝓞 E := ∏ i, s i with ht
    have htP : t ∉ P.asIdeal := by
      intro hm
      obtain ⟨i, -, h⟩ := (Ideal.IsPrime.prod_mem_iff (hp := P.isPrime)).1 hm
      exact hs i h
    have ht' : ∀ i, t • f (Pi.single i (1 : E)) ∈ N := by
      intro i
      rw [ht, ← Finset.prod_erase_mul _ s (Finset.mem_univ i), mul_smul]
      exact N.smul_mem _ (hs' i)
    let g : Sp E n →ₗ[E] Sp E n := (algebraMap (𝓞 E) E t) • (f : Sp E n →ₗ[E] Sp E n)
    refine ⟨(LinearMap.toMatrix' g).det, Submodule.subset_span ⟨LinearMap.toMatrix' g, ?_, rfl⟩, ?_⟩
    · intro v hv
      have h2 : (LinearMap.toMatrix' g).mulVec v = t • f v := by
        rw [LinearMap.toMatrix'_mulVec]
        simp [g]
      rw [h2]
      clear h2
      rw [stdLat_eq_span] at hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact ht' i
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact N.add_mem hx hy
      | smul r x _ hx =>
        rw [← algebraMap_smul E r x, map_smul, algebraMap_smul, smul_comm]
        exact N.smul_mem r hx
    · rw [LinearMap.det_toMatrix', LinearMap.det_smul, map_mul, map_pow,
        (HeightOneSpectrum.valuation_eq_one_iff_notMem P).2 htP, one_pow, one_mul]

end GlobalTheory.CharVal.DetFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemHomAtGmap
section
noncomputable section

namespace GlobalTheory.KerT.Bar

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT
open GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree (InBox)

section Box

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}

theorem mem_homAt_gmap (S : Finset (HeightOneSpectrum (𝓞 E))) (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b)
    (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) (x : HomE E a b) :
    x ∈ homAt S (gmap g N) (gmap g' N') ↔ g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap ∈ homAt S N N' := by
  constructor
  · intro h P hP y hy
    have := h P hP (g y) ((mem_localization_gmap _ _ _ _).2 (by simpa using hy))
    exact (mem_localization_gmap _ _ _ _).1 this
  · intro h P hP y hy
    have := h P hP (g.symm y) ((mem_localization_gmap _ _ _ _).1 hy)
    exact (mem_localization_gmap _ _ _ _).2 (by simpa using this)

theorem conj_osmul (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) (c : 𝓞 E) (x : HomE E a b) :
    g'.symm.toLinearMap ∘ₗ (c • x) ∘ₗ g.toLinearMap = c • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine LinearMap.ext fun y => ?_
  exact equiv_osmul g'.symm c (x (g y))

theorem inBox_gmap {K : Type} [Field K] {S : Finset (HeightOneSpectrum (𝓞 E))} {cA cB : ℕ}
    {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)} {Ξ : HomE E a b → K} (h : InBox S cA cB N N' Ξ)
    (g : Sp E a ≃ₗ[E] Sp E a) (g' : Sp E b ≃ₗ[E] Sp E b) :
    InBox S cA cB (gmap g N) (gmap g' N') fun x => Ξ (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) := by
  refine ⟨fun x hx => ?_, ?_⟩
  · have h1 : (cA : 𝓞 E) • (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) ∈ homAt S N N' := h.1 _ hx
    change (cA : 𝓞 E) • x ∈ homAt S (gmap g N) (gmap g' N')
    rw [mem_homAt_gmap, conj_osmul]
    exact h1
  · rintro x _ ⟨z, hz, rfl⟩
    have h1 := h.2 (g'.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ ⟨_, (mem_homAt_gmap S g g' N N' z).1 hz, rfl⟩
    change Ξ (g'.symm.toLinearMap ∘ₗ (x + (cB : 𝓞 E) • z) ∘ₗ g.toLinearMap) = _
    rw [LinearMap.add_comp, LinearMap.comp_add, conj_osmul]
    exact h1

end Box

variable {X : Fields}

theorem framed_gmap {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {N : Submodule (𝓞 X.E) (Sp X.E n)} {fr : Frs X.E n SB}
    (h : Framed N fr) (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) : Framed (gmap g N) (fun P : SB => g * fr P) := by
  intro P x
  rw [mem_localization_gmap, ← h P x]
  simp

theorem mem_valAt_gmap (w : HeightOneSpectrum (𝓞 X.K)) {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n)
    (L : Submodule (𝓞 X.E) (Sp X.E n)) (y : VV X.K lam) :
    y ∈ valAt w lam (gmap γ.1 L) ↔ ∃ z ∈ valAt w lam L, rhoVr X.emb lam (ufGL X.E n γ) z = y := by
  unfold valAt
  rw [delAtr_gmap, Formalism.BasicNotions.SkeletonIndexLemmas.localization_map₂]
  exact Iff.rfl

theorem rho_inv_apply {n : ℕ} (lam : X.Tau → DomWeight n) (γ : UF X.E n) (y : VV X.K lam) :
    rhoVr X.emb lam (ufGL X.E n γ⁻¹) (rhoVr X.emb lam (ufGL X.E n γ) y) = y := by
  rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]

theorem barTerm_of_std : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → RatTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) → ∀ w : HeightOneSpectrum (𝓞 Z.X.K), (∀ {SG SG' : Finset (HeightOneSpectrum (𝓞 Z.X.E))} (d : DecoSet (E := Z.X.E) (n := Z.R.N i) (ST := Z.Pr.vT u) (SG := SG)) (fr : Frs Z.X.E (Z.R.N i) (rowSG Z.Pr sel mu)) (d' : DecoSet (E := Z.X.E) (n := Z.R.N (i + 1)) (ST := Z.Pr.vT u) (SG := SG')) (fr' : Frs Z.X.E (Z.R.N (i + 1)) (rowSG Z.Pr sel mu)) (Ξ₀ : HomE Z.X.E (Z.R.N i) (Z.R.N (i + 1)) → Z.X.K), StdOnly u i (i + 1) d d' → Framed d.1.N fr → Framed d'.1.N fr' → InBoxOfRowSelection sel mu cst u d.1.N d'.1.N Ξ₀ → (∀ x, w.valuation Z.X.K (Ξ₀ x) ≤ 1) → ∀ y ∈ valAt w (Z.W.lamTrue u i) d.1.Lsh, ∃ y' ∈ valAt w (Z.W.lamTrue u (i + 1)) d'.1.Lsh, term Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) d fr d' fr' Ξ₀ y = ((Z.Pr.T u : Z.X.K) ^ (Z.X.f * ((Z.R.t + 1) / 2))) • y') → BarTerm Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) w := by
  intro Z H s cc δ B χ cD sel S mu cst u i _ hyp hrat w hstd SG SG' d fr d' fr' Ξ₀ hfr hfr' hbox hint y hy
  obtain ⟨γ, hγ⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG d
  obtain ⟨γ', hγ'⟩ := GlobalTheory.StdReps.representatives Z.X hyp.ok.fields Z.Pr hyp.ok.primes u _ SG' d'
  obtain ⟨y', hy', he⟩ := hstd (((γ, 1) : UF Z.X.E _ × GLG (E := Z.X.E) (n := _) (SG := SG)) • d) (fun P => γ.1 * fr P)
    (((γ', 1) : UF Z.X.E _ × GLG (E := Z.X.E) (n := _) (SG := SG')) • d') (fun P => γ'.1 * fr' P)
    (fun x => Ξ₀ (γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap))
    ⟨fun P => hγ P.1 P.2, fun P => hγ' P.1 P.2⟩ (framed_gmap hfr γ.1) (framed_gmap hfr' γ'.1)
    (inBox_gmap hbox γ.1 γ'.1) (fun x => hint _) (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ) y) (by
      rw [DecoSet.smul_val, Deco.Lsh_act _ γ.2, mem_valAt_gmap]
      exact ⟨y, hy, rfl⟩)
  rw [DecoSet.smul_val, Deco.Lsh_act _ γ'.2, mem_valAt_gmap] at hy'
  obtain ⟨z, hz, rfl⟩ := hy'
  refine ⟨z, hz, ?_⟩
  rw [hrat d fr d' fr' Ξ₀ γ γ' hbox, LinearMap.comp_apply, LinearMap.comp_apply, rho_inv_apply, ← map_smul] at he
  have h2 := congrArg (rhoVr Z.X.emb _ (ufGL Z.X.E _ γ'⁻¹)) he
  rwa [rho_inv_apply, rho_inv_apply] at h2

end GlobalTheory.KerT.Bar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentCompanion
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.MomentCompanion

theorem companion_gen {E : Type} [Field E] [NumberField E] [StarRing E] {b : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (ϖ : 𝓞 E) (d : DecoSet (E := E) (n := b) (ST := ST) (SG := SG))
    (hST : ∀ P : ST, ϖ ∈ P.1.asIdeal) (hcop : IsCoprime ϖ (cO E ϖ)) :
    ∃ N'' : Submodule (𝓞 E) (Sp E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : E) • y ∈ N'') ∧
      (∀ y ∈ N'', star (ϖ : E) • y ∈ d.1.N) ∧
      ∀ (P : ST) (y : Sp E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 := by
  have hd := d.2
  have hIN : Ideal.span {ϖ} • d.1.N ≤ d.1.L := by
    rw [Submodule.smul_le]
    intro r hr y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    exact hd.smul_N_mem_L (fun P => Ideal.mul_mem_left _ _ (hST P)) hy
  obtain ⟨h1, h2⟩ := glue_unimodular (I := Ideal.span {ϖ}) (J := Ideal.span {cO E ϖ})
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (fun p hp => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hp
      rw [map_mul, cO_cO]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
    (by
      obtain ⟨u, v, huv⟩ := hcop
      exact ⟨u * ϖ, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), v * cO E ϖ,
        Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), huv⟩)
    hd.uni hd.L_lattice hd.L_le_N hIN
  have hbar : ∀ x ∈ d.1.L ⊔ Ideal.span {ϖ} • dual (hStd E b) d.1.L, cO E ϖ • x ∈ d.1.L := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [smul_add]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ hy) ?_
    refine Submodule.smul_induction_on hz (fun r hr u hu => ?_) (fun u v hu hv => ?_)
    · rw [smul_comm]
      exact hIN (Submodule.smul_mem_smul hr (conj_smul_dual_mem hd.uni hIN
        (by rw [cO_cO]; exact Ideal.mem_span_singleton_self _) hu))
    · rw [smul_add]
      exact Submodule.add_mem _ hu hv
  refine ⟨_, ⟨h1, h2⟩, fun y hy => ?_, fun y hy => ?_, fun P y => ?_⟩
  · have : ϖ • y ∈ d.1.L := hd.smul_N_mem_L hST hy
    rw [← algebraMap_smul E ϖ y] at this
    exact Submodule.mem_sup_left this
  · have := hd.L_le_N (hbar y hy)
    rw [← algebraMap_smul E (cO E ϖ) y, algebraMap_cO] at this
    exact this
  · have hn : cO E ϖ ∉ P.1.asIdeal := by
      intro h
      obtain ⟨u, v, huv⟩ := hcop
      exact one_notMem P.1 (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ (hST P)) (Ideal.mul_mem_left _ _ h))
    rw [← hd.mem_locP_L P y]
    exact ⟨fun h => localization_le_of_smul_mem hn hbar h, fun h => localization_le_of_smul_mem (one_notMem P.1) (fun x hx => by
      rw [one_smul]; exact Submodule.mem_sup_left hx) h⟩

theorem companion : ∀ (X : Fields) (b : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (d : DecoSet (E := X.E) (n := b) (ST := divs ϖ) (SG := SG)), X.Ok → ϖ ≠ 0 → IsCoprime ϖ (X.conjO ϖ) → (∀ P ∈ divs ϖ, ϖ ∉ P.asIdeal ^ 2) → ∃ N'' : Submodule (𝓞 X.E) (Sp X.E b), IsSdLat N'' ∧ (∀ y ∈ d.1.N, (ϖ : X.E) • y ∈ N'') ∧ (∀ y ∈ N'', star (ϖ : X.E) • y ∈ d.1.N) ∧ ∀ (P : ↥(divs ϖ)) (y : Sp X.E b), y ∈ localization₂ P.1.asIdeal N'' ↔ y ∈ d.1.at P.1 ∧ d.1.f P y = 0 :=
  fun _ _ _ ϖ d _ h0 hcop _ => companion_gen ϖ d (fun P => (mem_divs h0 P.1).1 P.2) hcop

end GlobalTheory.MomT.MomentCompanion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MonomialEqSumJet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MonoJet

open GlobalTheory.Proof.DirectionalDerivative GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets MvPowerSeries

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {N N' : ℕ}

theorem embT_injective : Function.Injective (TaylorLogMetric.embT D) := by
  intro τ τ' h
  apply D.eTau.injective
  apply (GlobalTheory.InducedType.galK_bijective D.host).1
  refine AlgEquiv.ext fun x => D.host.φ₀.injective ?_
  exact congrArg (fun f : D.host.E →+* ℂ => f x) h

theorem lamC_injOn {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) (h : TaylorLogMetric.lamC lam x = TaylorLogMetric.lamC lam y) : x = y := by
  rw [TaylorLogMetric.lamC, TaylorLogMetric.lamC, dite_eq_left hx, dite_eq_left hy] at h
  exact congrArg Subtype.val (lam.injective h)

theorem emb_mem {A : Type} [Field A] [NumberField A] (f : A →+* ℂ) (x : A) : f x ∈ TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom f.toRatAlgHom)

theorem lamC_add {x y : ℂ} (hx : x ∈ TaylorLogMetric.Qbar) (hy : y ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (x + y) = TaylorLogMetric.lamC lam x + TaylorLogMetric.lamC lam y := by
  rw [TaylorLogMetric.lamC, TaylorLogMetric.lamC, TaylorLogMetric.lamC, dite_eq_left hx, dite_eq_left hy, dite_eq_left (add_mem hx hy), ← map_add (f := _)]
  rfl

theorem lamC_sum {ι : Type} (s : Finset ι) (f : ι → ℂ) (hf : ∀ i, f i ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam (∑ i ∈ s, f i) = ∑ i ∈ s, TaylorLogMetric.lamC lam (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, TaylorLogMetric.lamC, dite_eq_left (zero_mem _)]
    exact map_zero lam
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lamC_add lam (hf a) (sum_mem fun i _ => hf i), ih]

theorem exists_single (τ : D.what₂.Tau) : ∃ (k : ℕ) (γ : Fin k → ℂ_[p]) (x : Fin k → D.host.E),
    (∑ l, γ l * TaylorLogMetric.tauEmb D lam τ (x l) = 1) ∧ ∀ τ', τ' ≠ τ → ∑ l, γ l * TaylorLogMetric.tauEmb D lam τ' (x l) = 0 := by
  classical
  choose g hg using fun τ => exists_lamHom lam (TaylorLogMetric.embT D τ)
  have hinj : Function.Injective fun τ => (g τ : D.host.E →* ℂ_[p]) := by
    intro a b h
    apply embT_injective D
    refine RingHom.ext fun x => lamC_injOn lam (emb_mem _ _) (emb_mem _ _) ?_
    rw [hg, hg]
    exact congrArg (fun f : D.host.E →* ℂ_[p] => f x) h
  have hli : LinearIndependent ℂ_[p] fun τ => (g τ : D.host.E → ℂ_[p]) :=
    (linearIndependent_monoidHom D.host.E ℂ_[p]).comp _ hinj
  have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
  have hm : (Pi.single τ 1 : D.what₂.Tau → ℂ_[p]) ∈
      Submodule.span ℂ_[p] (Set.range (flip fun τ => (g τ : D.host.E → ℂ_[p]))) := hsp ▸ Submodule.mem_top
  obtain ⟨k, γ, v, hv⟩ := Submodule.mem_span_set'.1 hm
  choose x hx using fun l => (v l).2
  have key : ∀ τ', ∑ l, γ l * TaylorLogMetric.tauEmb D lam τ' (x l) = (Pi.single τ 1 : D.what₂.Tau → ℂ_[p]) τ' := by
    intro τ'
    rw [← hv, Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Pi.smul_apply, ← hx l, TaylorLogMetric.tauEmb, hg]
    rfl
  exact ⟨k, γ, x, by rw [key, Pi.single_eq_same], fun τ' h => by rw [key, Pi.single_eq_of_ne h]⟩


open Classical in
theorem exists_vecY (v : D.what₂.Tau × Fin N' × Fin N) : ∃ (k : ℕ) (γ : Fin k → ℂ_[p])
    (z : Fin k → Matrix (Fin N') (Fin N) D.host.E), ∑ l, γ l • vecY D lam (z l) = Pi.single v 1 := by
  obtain ⟨τ, i, j⟩ := v
  obtain ⟨k, γ, x, h1, h2⟩ := exists_single D lam τ
  refine ⟨k, γ, fun l => Matrix.single i j (x l), ?_⟩
  funext ⟨τ', i', j'⟩
  obtain ⟨g, hg⟩ := exists_lamHom lam (TaylorLogMetric.embT D τ')
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vecY]
  by_cases hij : i = i' ∧ j = j'
  · obtain ⟨rfl, rfl⟩ := hij
    simp only [Matrix.single_apply_same]
    by_cases hτ : τ' = τ
    · subst hτ
      rw [h1, Pi.single_eq_same]
    · rw [h2 τ' hτ, Pi.single_eq_of_ne (fun h => hτ (congrArg Prod.fst h))]
  · rw [Pi.single_eq_of_ne (fun h => hij (by simp only [Prod.mk.injEq] at h; exact ⟨h.2.1.symm, h.2.2.symm⟩))]
    simp only [TaylorLogMetric.tauEmb, hg]
    simp [Matrix.single_apply_of_ne _ _ _ _ _ hij]

theorem lam_hYY (y Y : Matrix (Fin N') (Fin N) D.host.E) :
    TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D y Y : D.host.K) : D.host.E)) =
      ∑ k : D.what₂.Tau × Fin N' × Fin N, vecY D lam y k * TaylorLogMetric.lamC lam (TaylorLogMetric.embT D k.1 (D.host.conj (Y k.2.1 k.2.2))) := by
  rw [TaylorLogMetric.hYY, ← GlobalTheory.InducedType.sum_eq_trace D, lamC_sum lam _ _ fun τ => emb_mem _ _, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  obtain ⟨g, hg⟩ := exists_lamHom lam (TaylorLogMetric.embT D τ)
  rw [hg]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vecY, TaylorLogMetric.tauEmb, hg, map_sum, map_mul, Fintype.sum_prod_type]

theorem dirDer_sum {σ ι : Type} [Fintype σ] (s : Finset ι) (c : ι → ℂ_[p]) (w : ι → σ → ℂ_[p]) :
    dirDer (∑ l ∈ s, c l • w l) = ∑ l ∈ s, c l • dirDer (w l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dirDer_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dirDer_add, dirDer_smul, ih]

theorem dirDer_single {σ : Type} [Fintype σ] [DecidableEq σ] (v : σ) (F : MvPowerSeries σ ℂ_[p]) :
    dirDer (Pi.single v 1) F = pderiv (R := ℂ_[p]) v F := by
  rw [dirDer_apply, Finset.sum_eq_single v]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem jet_eq {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    TaylorLogMetric.jet D lam y F = constantCoeff (derList D lam (List.ofFn y) F) := by
  rw [TaylorLogMetric.jet, foldr_der]

theorem jet_snoc {n : ℕ} (y : Fin n → Matrix (Fin N') (Fin N) D.host.E) (z : Matrix (Fin N') (Fin N) D.host.E)
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    TaylorLogMetric.jet D lam (Fin.snoc y z : Fin (n + 1) → _) F =
      constantCoeff (derList D lam (List.ofFn y) (dirDer (vecY D lam z) F)) := by
  rw [jet_eq, List.ofFn_succ_last]
  simp [derList]

theorem exists_comb (n : ℕ) : ∀ α : TaylorLogMetric.Mono D N N', α.degree = n →
    ∃ (ι : Type) (_ : Fintype ι) (γ : ι → ℂ_[p]) (y : ι → Fin n → Matrix (Fin N') (Fin N) D.host.E),
    (∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], jetAt F α = ∑ l, γ l * TaylorLogMetric.jet D lam (y l) F) ∧
    ∀ Y : Matrix (Fin N') (Fin N) D.host.E,
      (α.prod fun v n => TaylorLogMetric.lamC lam (TaylorLogMetric.embT D v.1 (D.host.conj (Y v.2.1 v.2.2))) ^ n) =
        ∑ l, γ l * ∏ j, TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (y l j) Y : D.host.K) : D.host.E)) := by
  classical
  induction n with
  | zero =>
    intro α hn
    rw [(Finsupp.degree_eq_zero_iff α).1 hn]
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ => Fin.elim0, fun F => ?_, fun Y => ?_⟩
    · simp [jetAt_zero, TaylorLogMetric.jet]
    · simp
  | succ n ih =>
    intro α hn
    have hα : α ≠ 0 := by rintro rfl; simp at hn
    obtain ⟨x, hx⟩ := Finsupp.support_nonempty_iff.2 hα
    have hle : Finsupp.single x 1 ≤ α := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hx)
    obtain ⟨β, rfl⟩ : ∃ β, α = β + Finsupp.single x 1 := ⟨α - Finsupp.single x 1, (tsub_add_cancel_of_le hle).symm⟩
    have hβ : β.degree = n := by
      rw [map_add (f := _), Finsupp.degree_single] at hn
      omega
    obtain ⟨ι, _, γ, y, h1, h2⟩ := ih β hβ
    obtain ⟨k, δ, z, hz⟩ := exists_vecY D lam x
    refine ⟨ι × Fin k, inferInstance, fun l => γ l.1 * δ l.2, fun l => Fin.snoc (y l.1) (z l.2), fun F => ?_, fun Y => ?_⟩
    · rw [jetAt_add_single, h1, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← dirDer_single, ← hz, dirDer_sum, jet_eq]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [jet_snoc, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, constantCoeff_smul,
        smul_eq_mul, Finset.mul_sum, mul_assoc]
    · rw [Finsupp.prod_add_index' (by simp) (fun _ _ _ => pow_add _ _ _), h2, Finsupp.prod_single_index (by simp),
        pow_one, Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      have e : TaylorLogMetric.lamC lam (TaylorLogMetric.embT D x.1 (D.host.conj (Y x.2.1 x.2.2))) =
          ∑ m, δ m * TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (z m) Y : D.host.K) : D.host.E)) := by
        simp only [lam_hYY, Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [← mul_assoc, ← Finset.sum_mul]
        have : ∀ v, ∑ m, δ m * vecY D lam (z m) v = (Pi.single x 1 : _ → ℂ_[p]) v := fun v => by
          rw [← hz, Finset.sum_apply]; rfl
        simp only [this]
        rw [Finset.sum_eq_single x]
        · simp
        · intro b _ hb
          simp [Pi.single_eq_of_ne hb]
        · simp
      rw [e, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
      ring

theorem monomial_eq_sum_jet : ∀ (D : D7) (p N N' : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (α : TaylorLogMetric.Mono D N N'), ∃ (k : ℕ) (γ : Fin k → ℂ_[p]) (y : Fin k → Fin α.degree → Matrix (Fin N') (Fin N) D.host.E), (∀ F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p], (α.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff α F = ∑ l, γ l * TaylorLogMetric.jet D lam (y l) F) ∧ ∀ Y : Matrix (Fin N') (Fin N) D.host.E, (α.prod fun v n => TaylorLogMetric.lamC lam (TaylorLogMetric.embT D v.1 (D.host.conj (Y v.2.1 v.2.2))) ^ n) = ∑ l, γ l * ∏ j, TaylorLogMetric.lamC lam (D.host.φ₀ ((TaylorLogMetric.hYY D (y l j) Y : D.host.K) : D.host.E)) := by
  intro D p N N' _ lam α
  obtain ⟨ι, _, γ, y, h1, h2⟩ := exists_comb D lam _ α rfl
  let e := (Fintype.equivFin ι).symm
  refine ⟨_, γ ∘ e, y ∘ e, fun F => ?_, fun Y => ?_⟩
  · exact (h1 F).trans (e.sum_comp _).symm
  · exact (h2 Y).trans (e.sum_comp _).symm

end GlobalTheory.MonoJet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
section
noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open _root_.Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

theorem mem_valO_of_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L)
    (W : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : ∀ r : 𝓞 K, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom j r ∈ W.asIdeal) (x : K) :
    j x ∈ valO W ↔ x ∈ valO Q := by
  letI : Algebra K L := j.toAlgebra
  haveI : W.asIdeal.LiesOver Q.asIdeal := ⟨Ideal.ext fun r => h r⟩
  rw [mem_valO, mem_valO, show j x = algebraMap K L x from rfl,
    ← HeightOneSpectrum.valuation_liesOver L Q W x]
  exact pow_le_one_iff (Ideal.ramificationIdx_pos_of_isDedekindDomain' W.asIdeal Q.ne_bot).ne'

theorem mem_Ow_iff_valO (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) : x ∈ Ow D w ↔ x ∈ valO (D.plEq w) :=
  D.val_nonneg_iff w x

theorem resChar_mem_plEq (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar', ← WithZero.exp_zero,
    WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

theorem resChar_eq_of_mem_plEq (D : D7) (w : D.what₂.places.Pl) {T : ℕ} (hT : T.Prime)
    (h : (T : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = T := by
  by_contra hne
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (T : 𝓞 D.what₂.LL) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.what₂.places.resChar_prime w) hT).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem_plEq D w)) (Ideal.mul_mem_left _ _ h)

end GlobalTheory.LvT.Inh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaZeroNorm
section
noncomputable section

namespace GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation

theorem normTheta0 : GlobalTheory.IndefiniteRowSideFullHecke.JacobiThetaHalfCharacteristic.NormTheta0 := GlobalTheory.ThetaNullNormSquares.normTheta0

end GlobalTheory.Proof.ThetaZeroNormGlobalInterpolation
end
end

