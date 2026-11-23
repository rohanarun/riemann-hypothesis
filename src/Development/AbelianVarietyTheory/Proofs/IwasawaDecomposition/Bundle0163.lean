module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsJunkLiftNotVanishing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0146

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowerEmbF
section
noncomputable section

namespace GlobalTheory.Mem.Col2.KerRat

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

theorem sum_cover {K M G D G' D' : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] [MulAction G D] [Group G']
    [MulAction G' D'] [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient G' D')]
    (π : D → D') (hs : Function.Surjective π) (h1 : ∀ (g : G) d, ∃ g' : G', π (g • d) = g' • π d)
    (h2 : ∀ (g' : G') d e, g' • π d = π e → ∃ g : G, g • d = e)
    (h3 : ∀ d, Nat.card (MulAction.stabilizer G d) = Nat.card (MulAction.stabilizer G' (π d)))
    (r : MulAction.orbitRel.Quotient G D → D) (hr : ∀ q, Quotient.mk (MulAction.orbitRel G D) (r q) = q)
    (r' : MulAction.orbitRel.Quotient G' D' → D') (hr' : ∀ q, Quotient.mk (MulAction.orbitRel G' D') (r' q) = q)
    (f : D' → M) (hf : ∀ (g' : G') d, f (g' • d) = f d) :
    ∑ q, ((Nat.card (MulAction.stabilizer G (r q)) : ℕ) : K)⁻¹ • f (π (r q)) =
      ∑ q, ((Nat.card (MulAction.stabilizer G' (r' q)) : ℕ) : K)⁻¹ • f (r' q) := by
  refine Fintype.sum_bijective (fun q => Quotient.mk (MulAction.orbitRel G' D') (π (r q))) ⟨fun q q' h => ?_, fun q' => ?_⟩ _ _
    fun q => ?_
  · obtain ⟨g', hg⟩ : ∃ g' : G', g' • π (r q') = π (r q) := Quotient.exact h
    obtain ⟨g, hg⟩ := h2 g' _ _ hg
    rw [← hr q, ← hr q']
    exact Quotient.sound ⟨g, hg⟩
  · obtain ⟨d, hd⟩ := hs (r' q')
    refine ⟨Quotient.mk _ d, ?_⟩
    obtain ⟨g, hg⟩ : ∃ g : G, g • d = r (Quotient.mk _ d) := Quotient.exact (hr (Quotient.mk _ d))
    obtain ⟨g', hg'⟩ := h1 g d
    rw [← hr' q', ← hd]
    exact Quotient.sound ⟨g', by rw [← hg, hg']⟩
  · obtain ⟨g', hg⟩ : ∃ g' : G', g' • π (r q) = r' (Quotient.mk _ (π (r q))) := Quotient.exact (hr' (Quotient.mk _ (π (r q))))
    rw [← hg, hf, h3, Nat.card_congr (MulAction.stabilizerEquivStabilizer (G := G') (a := π (r q)) (b := g' • π (r q)) (g := g') rfl).toEquiv]

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  (I : ChainIn E K ι R) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R) (hI : I.Ok)

abbrev PtKer : Type := ∀ i b b', (I.S i).D b → (I.S (i + 1)).D b' → (VV K (lamT hc i) →ₗ[K] VV K (lamT hc (i + 1)))

abbrev ev (i : ℕ) : VV K (lamT hc i) →ₛₗ[σ] (Fr emb σ (R.N i) → ℂ) :=
  evV emb (1 : Matrix (Fin (R.N i)) (Fin (R.N i)) E) (lamT hc i) σ

variable {I hc} (k : PtKer I hc)

def EqTarget (i : ℕ) : Prop := ∀ b b' (g' : (I.S (i + 1)).G b') d d',
  k i b b' d (g' • d') = (I.S (i + 1)).rho emb (lamT hc (i + 1)) b' g' ∘ₗ k i b b' d d'

def ReadsAt (i : ℕ) : Prop := ∀ c c' F, (I.chain emb σ hI hc).Kmap i c c' (ev emb σ hc i F) =
  ev emb σ hc (i + 1) (k i c.1 c'.1 ((I.S i).rep c) ((I.S (i + 1)).rep c') F)

def stepPt (i : ℕ) (x : (I.S i).Cl → VV K (lamT hc i)) (b' : (I.S (i + 1)).β) (d' : (I.S (i + 1)).D b') : VV K (lamT hc (i + 1)) :=
  letI := I.clFin hI i
  ∑ c : (I.S i).Cl, ((Nat.card ((I.S i).Stab c) : ℕ) : K)⁻¹ • k i c.1 b' ((I.S i).rep c) d' (x c)

def colPt (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) (j : ℕ) : ∀ b, (I.S j).D b → VV K (lamT hc j) :=
  Nat.rec (motive := fun j => ∀ b, (I.S j).D b → VV K (lamT hc j)) φ
    (fun j ψ => stepPt hI k j fun c => ψ c.1 ((I.S j).rep c)) j

variable {emb k}

theorem stepPt_smul {i : ℕ} (h : EqTarget emb k i) (x : (I.S i).Cl → VV K (lamT hc i)) (b' : (I.S (i + 1)).β)
    (g' : (I.S (i + 1)).G b') (d' : (I.S (i + 1)).D b') :
    stepPt hI k i x b' (g' • d') = (I.S (i + 1)).rho emb (lamT hc (i + 1)) b' g' (stepPt hI k i x b' d') := by
  unfold stepPt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h, map_smul]
  rfl

theorem colPt_smul (h : ∀ i, i < R.m → EqTarget emb k i) (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) {j : ℕ} (h0 : 0 < j) (hj : j ≤ R.m)
    (b : (I.S j).β) (g : (I.S j).G b) (d : (I.S j).D b) :
    colPt hI k φ j b (g • d) = (I.S j).rho emb (lamT hc j) b g (colPt hI k φ j b d) := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  exact stepPt_smul hI (h i (by omega)) _ b g d

variable {σ hI}

theorem K_ev {i : ℕ} (h : ReadsAt emb σ hI k i) (x : (I.S i).Cl → VV K (lamT hc i)) :
    (I.chain emb σ hI hc).K i (fun c => ev emb σ hc i (x c)) =
      fun c' => ev emb σ hc (i + 1) (stepPt hI k i x c'.1 ((I.S (i + 1)).rep c')) := by
  funext c'
  unfold stepPt
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [LinearMap.map_smulₛₗ, map_inv₀, map_natCast, ← h]
  rfl

theorem chain_ev (h : ∀ i, i < R.m → ReadsAt emb σ hI k i) (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) {j : ℕ} (hj : j ≤ R.m) :
    letI := (I.chain emb σ hI hc).clsFin
    Formalism.ThetaLiftIndependence.chainOpM (I.chain emb σ hI hc).wt (I.chain emb σ hI hc).Kmap j (fun c => ev emb σ hc 0 (φ c.1 ((I.S 0).rep c))) =
      fun c => ev emb σ hc j (colPt hI k φ j c.1 ((I.S j).rep c)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    refine Eq.trans ?_ (K_ev (h j (by omega)) fun c => colPt hI k φ j c.1 ((I.S j).rep c))
    rw [← ih (by omega)]
    rfl

theorem exists_K_embF {i : ℕ} (h : ReadsAt emb σ hI k i) (h' : EqTarget emb k i) (hF : ((I.S i).fam emb (lamT hc i)).Ok)
    (hF' : ((I.S (i + 1)).fam emb (lamT hc (i + 1))).Ok) (x : (I.S i).FormsK emb (lamT hc i) hF) :
    ∃ y, (I.S (i + 1)).embF emb σ (lamT hc (i + 1)) hF' y = (I.chain emb σ hI hc).K i ((I.S i).embF emb σ (lamT hc i) hF x) :=
  ⟨⟨fun c' => stepPt hI k i x.1 c'.1 ((I.S (i + 1)).rep c'), fun c' g =>
    (stepPt_smul hI h' x.1 c'.1 g.1 _).symm.trans (congrArg (stepPt hI k i x.1 c'.1) g.2)⟩, (K_ev h x.1).symm⟩

variable (Q : PerIn I) (hQ : Q.Ok)

theorem lower_ev (x : (I.S R.m).Cl → VV K (lamT hc R.m)) (c : Q.S'.Cl) :
    (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz fun c => ev emb σ hc R.m (x c)) c =
      evV emb (1 : Matrix (Fin (R.N R.m - 1)) (Fin (R.N R.m - 1)) E) Q.sgT σ
        (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
          ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x (Q.tilC c)))) := by
  show fnOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) 1 (Q.br emb σ hc
      (polOf (Gr emb σ (R.N R.m)) (shiftOf (lamT hc R.m)) (fr0 emb σ (R.N R.m))
        ((I.S R.m).tr emb σ Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
          (evV emb (1 : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) (lamT hc R.m) σ (x (Q.tilC c)))))) = _
  rw [← LvT.BuiltChain.evV_rho, LvT.BuiltChain.polOf_evV, LvT.BuiltChain.br_map]
  rfl

theorem exists_lower_embF (hW : ∀ τ, Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ))
    (hS : ∀ τ, Br.SameShift (lamT hc R.m τ) (Q.sgT τ)) (hF : ((I.S R.m).fam emb (lamT hc R.m)).Ok) (hP : (Q.S'.fam emb Q.sgT).Ok)
    (x : (I.S R.m).FormsK emb (lamT hc R.m) hF) :
    ∃ y, Q.S'.embF emb σ Q.sgT hP y =
      (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz ((I.S R.m).embF emb σ (lamT hc R.m) hF x)) := by
  let v : Q.S'.Cl → VV K (lamT hc R.m) := fun c =>
    (I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c))
  let B := Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
  refine ⟨⟨fun c => B (v c), fun c g => ?_⟩, funext fun c => (lower_ev Q hQ x.1 c).symm⟩
  have h1 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 *
      (I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c)) = x.1 (Q.tilC c) := x.2 (Q.tilC c) (Q.stabMap hQ c g)
  have h2 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (Q.ext c.1 g.1) (v c) = v c := by
    have h3 := congrArg ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))) h1
    rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
    exact h3
  show ((Q.S'.chr c.1 g.1 : Kˣ) : K) • rhoVr emb Q.sgT (Q.S'.gam c.1 g.1) (B (v c)) = B (v c)
  rw [← LvT.BuiltChain.brAt_rhoVr emb (N_m_succ R) hW hS _ (Q.S'.gam c.1 g.1) ((I.S R.m).gam Q.b0 (Q.ext c.1 g.1))
    (fun z => by rw [← map_inv, ← map_inv, ← map_inv]; exact hQ.gam_ini _ _ z)
    (fun z => by rw [← map_inv, ← map_inv]; exact hQ.gam_last _ _ z), ← map_smul, ← hQ.chr_ext]
  exact congrArg B h2

theorem ptilCol_ev (h : ∀ i, i < R.m → ReadsAt emb σ hI k i) (h' : ∀ i, i < R.m → EqTarget emb k i)
    (φ : ∀ b, (I.S 0).D b → VV K (lamT hc 0)) (F : Q.Mt emb σ) (y : Q.S'.Cl → VV K Q.sgT)
    (hy : ∀ c, Q.rd emb σ F c = MvPolynomial.map σ (y c).1) :
    (Q.per emb σ hI hQ hc).PtilCol (fun c => ev emb σ hc 0 (φ c.1 ((I.S 0).rep c))) F = letI := Q.clFin hQ
      σ (∑ c : Q.S'.Cl, ((Nat.card (Q.S'.Stab c) : ℕ) : K)⁻¹ • pairBK Q.sgT
        (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz) (colPt hI k φ R.m Q.b0 (Q.tilPt c))) (y c)) := by
  unfold PeriodMap.PtilCol PeriodMap.Ptil ColumnChain.col
  rw [chain_ev h φ le_rfl]
  have e := funext (lower_ev (σ := σ) (emb := emb) (hI := hI) Q hQ fun c => colPt hI k φ R.m c.1 ((I.S R.m).rep c))
  refine (congrArg (fun z => (Q.per emb σ hI hQ hc).period z F) e).trans ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul, map_inv₀, map_natCast]
  refine Finset.sum_congr rfl fun c _ => congrArg _ ?_
  have e2 := colPt_smul hI h' φ (lt_of_lt_of_le (by norm_num) R.two_le_m) le_rfl Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
    ((I.S R.m).rep ((I.S R.m).cl Q.b0 (Q.tilPt c)))
  rw [GStep.mv_smul] at e2
  rw [pairBK_apply, PeriodOnStep.map_pairB, ← hy, ← PeriodOnStep.polOf_evV σ emb, e2]
  rfl

end GlobalTheory.Mem.Col2.KerRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroAdeleCharEqCompMulTotallyReal
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.AdeleCharTwist

theorem exists_eq_exp (g : ℝ → ℂ) (hc : Continuous g) (hn : ∀ t, ‖g t‖ = 1) (h0 : g 0 = 1)
    (hadd : ∀ s t, g (s + t) = g s * g t) :
    ∃ c : ℝ, ∀ t : ℝ, g t = Complex.exp (2 * Real.pi * Complex.I * ((c * t : ℝ) : ℂ)) := by
  have hm : ∀ a, g a ∈ Submonoid.unitSphere ℂ := fun a => by simpa [Submonoid.unitSphere] using hn a
  let χ : C(ℝ, Circle) := ⟨fun a => ⟨g a, hm a⟩, hc.subtype_mk hm⟩
  have hχ : ∀ s t, χ (s + t) = χ s * χ t := fun s t => Subtype.ext (hadd s t)
  obtain ⟨L, ⟨hL0, hL⟩, hu⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts χ 0 0
    (by rw [Circle.exp_zero]; exact Subtype.ext h0.symm)
  have hL' : ∀ t, Circle.exp (L t) = χ t := congrFun hL
  have hLa : ∀ s t, L (s + t) = L s + L t := fun s t => by
    have := hu ⟨fun t => L (s + t) - L s, by fun_prop⟩ ⟨by simp, by
      funext t
      show Circle.exp (L (s + t) - L s) = χ t
      rw [Circle.exp_sub, hL', hL', hχ, mul_div_cancel_left]⟩
    have h2 : L (s + t) - L s = L t := DFunLike.congr_fun this t
    linarith
  let l : ℝ →+ ℝ := AddMonoidHom.mk' L hLa
  refine ⟨L 1 / (2 * Real.pi), fun t => ?_⟩
  have h3 : L t = t * L 1 := by
    have := map_real_smul l L.continuous t 1
    simpa [l] using this
  have h4 : g t = (Circle.exp (L t) : ℂ) := by rw [hL']; rfl
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [h4, Circle.coe_exp, h3]
  congr 1
  push_cast
  field_simp

variable {F : Type} [Field F] [NumberField F]

theorem pairA_add (x x' : Ainf F) (y y' : Af F) :
    pairA F (x + x') (y + y') = pairA F x y + pairA F x' y' := rfl

theorem algebraMap_eq_pairA (x : F) :
    algebraMap F (AF F) x = pairA F (algebraMap F _ x) 0 + pairA F 0 (algebraMap F _ x) := by
  rw [← pairA_add, add_zero, zero_add]
  rfl

theorem denseRange_fin : DenseRange (algebraMap F (Af F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : Af F => y - z := continuous_const.sub continuous_id
  have hV : (fun z : Af F => y - z) ⁻¹' U ∈ 𝓝 (0 : Af F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ hV
  obtain ⟨a, β, hβ, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨y - N • β, hNU β hβ, a, ?_⟩
  rw [e, add_sub_cancel_right]

theorem ext_of_inf {ψ ψ' : AF F → ℂ} (hc : Continuous ψ) (hc' : Continuous ψ')
    (ha : ∀ x y, ψ (x + y) = ψ x * ψ y) (ha' : ∀ x y, ψ' (x + y) = ψ' x * ψ' y)
    (hr : ∀ a : F, ψ (algebraMap F _ a) = 1) (hr' : ∀ a : F, ψ' (algebraMap F _ a) = 1)
    (h : ∀ a : F, ψ (pairA F (algebraMap F _ a) 0) = ψ' (pairA F (algebraMap F _ a) 0)) (x : AF F) :
    ψ x = ψ' x := by
  have h1 : (fun z => ψ (pairA F z 0)) = fun z => ψ' (pairA F z 0) :=
    (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      (hc.comp (continuous_id.prodMk continuous_const)) (hc'.comp (continuous_id.prodMk continuous_const))
      (funext h)
  have h2 : (fun z => ψ (pairA F 0 z)) = fun z => ψ' (pairA F 0 z) :=
    denseRange_fin.equalizer
      (hc.comp (continuous_const.prodMk continuous_id)) (hc'.comp (continuous_const.prodMk continuous_id))
      (funext fun a => by
        have e := hr a
        have e' := hr' a
        rw [algebraMap_eq_pairA, ha, h] at e
        rw [algebraMap_eq_pairA, ha'] at e'
        exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one e) (e.trans e'.symm))
  have e : x = pairA F x.1 0 + pairA F 0 x.2 := by
    rw [← pairA_add, add_zero, zero_add]
    rfl
  rw [e, ha, ha', congrFun h1, congrFun h2]

theorem exists_nsmul_inf {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ N : ℕ, 0 < N ∧ ∀ r : 𝓞 F, ψ (pairA F (algebraMap F _ ((N : F) * r)) 0) = 1 := by
  obtain ⟨N, hN, h⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ (GlobalTheory.FinTranslate.ker_mem_nhds hψ.1 hψ.2.1)
  refine ⟨N, hN, fun r => ?_⟩
  have h1 : ψ (pairA F 0 (N • algebraMap F (Af F) r)) = 1 :=
    h _ fun v => HeightOneSpectrum.coe_mem_adicCompletionIntegers v r
  have h2 := hψ.2.2.1 ((N : F) * r)
  rw [nsmul_eq_mul, ← map_natCast (algebraMap F (Af F)), ← map_mul] at h1
  rwa [algebraMap_eq_pairA, AddChar.map_add_eq_mul, h1, mul_one] at h2

theorem exists_realHom [IsTotallyReal F] : ∃ ρ : ℝ →+* Ainf F, Continuous ρ := by
  let e : ∀ w : InfinitePlace F, w.Completion ≃+* ℝ := fun w =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
  exact ⟨Pi.ringHom fun w => (e w).symm.toRingHom, continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous⟩

theorem exists_trace [IsTotallyReal F] {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) :
    ∃ a : F, ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ)) := by
  classical
  obtain ⟨N, hN, hNr⟩ := exists_nsmul_inf hψ
  obtain ⟨ρ, hρ⟩ := exists_realHom (F := F)
  have hρq : ∀ q : ℚ, ρ (q : ℝ) = algebraMap F (Ainf F) (q : F) := fun q =>
    RingHom.congr_fun (RingHom.ext_rat (ρ.comp (Rat.castHom ℝ)) ((algebraMap F (Ainf F)).comp (Rat.castHom F))) q
  have hadd : ∀ x y : Ainf F, ψ (pairA F (x + y) 0) = ψ (pairA F x 0) * ψ (pairA F y 0) := fun x y => by
    rw [← AddChar.map_add_eq_mul, ← pairA_add, add_zero]
  have h0 : ψ (pairA F 0 0) = 1 := ψ.map_zero_eq_one
  have key : ∀ r : 𝓞 F, ∃ c : ℚ, ∀ q : ℚ, ψ (pairA F (algebraMap F _ (q • (r : F))) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((q * c : ℚ) : ℂ)) := fun r => by
    obtain ⟨c, hc⟩ := exists_eq_exp (fun t => ψ (pairA F (ρ t * algebraMap F _ (r : F)) 0))
      (hψ.1.comp ((hρ.mul continuous_const).prodMk continuous_const)) (fun t => hψ.2.1 _)
      (by simp only [map_zero, zero_mul, h0]) (fun s t => by simp only [map_add (f := _), add_mul, hadd])
    have hq : ∀ q : ℚ, ψ (pairA F (algebraMap F _ ((q : F) * (r : F))) 0) =
        Complex.exp (2 * Real.pi * Complex.I * ((c * q : ℝ) : ℂ)) := fun q => by
      rw [← hc, hρq, map_mul]
    have h1 := hq N
    rw [Rat.cast_natCast, hNr, eq_comm, Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    rw [mul_comm (n : ℂ), mul_right_inj' Complex.two_pi_I_ne_zero] at hn
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    refine ⟨n / N, fun q => ?_⟩
    rw [Rat.smul_def, hq]
    congr 2
    push_cast at hn ⊢
    rw [← hn]
    field_simp
  choose c hc using key
  let b := integralBasis F
  let φ : F →ₗ[ℚ] ℚ := b.constr ℚ fun i => c (RingOfIntegers.basis F i)
  obtain ⟨a, ha⟩ := ((Algebra.traceForm ℚ F).toDual (traceForm_nondegenerate ℚ F)).surjective φ
  have ha' : ∀ x, Algebra.trace ℚ F (a * x) = φ x := fun x => by
    rw [← ha]; rfl
  refine ⟨a, fun x => ?_⟩
  rw [ha', ← b.sum_repr x]
  refine Finset.sum_induction _ (fun y : F => ψ (pairA F (algebraMap F _ y) 0) =
    Complex.exp (2 * Real.pi * Complex.I * ((φ y : ℚ) : ℂ))) (fun y z hy hz => ?_) ?_ fun i _ => ?_
  · rw [map_add (f := _), hadd, hy, hz, map_add (f := _), ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · simp only [map_zero, h0, Rat.cast_zero, mul_zero, Complex.exp_zero]
  · rw [map_smul φ, Module.Basis.constr_basis, smul_eq_mul, ← hc, integralBasis_apply]

theorem trace_mul_ne_zero {ψ : AddChar (AF F) ℂ} (hψ : IsCharAF F ψ) {a : F}
    (h : ∀ x : F, ψ (pairA F (algebraMap F _ x) 0) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F (a * x) : ℚ) : ℂ))) : a ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := hψ.2.2.2
  refine hx (ext_of_inf (ψ' := fun _ => 1) hψ.1 continuous_const ψ.map_add_eq_mul (fun _ _ => by simp)
    hψ.2.2.1 (fun _ => rfl) (fun y => by simp [h]) x)

theorem exists_mul_eq : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ψ ψ' : AddChar (AF F) ℂ), IsCharAF F ψ → IsCharAF F ψ' → ∃ a : F, a ≠ 0 ∧ ∀ x, ψ' x = ψ (algebraMap F (AF F) a * x) := by
  intro F _ _ _ ψ ψ' hψ hψ'
  obtain ⟨a, ha⟩ := exists_trace hψ
  obtain ⟨a', ha'⟩ := exists_trace hψ'
  have h0 := trace_mul_ne_zero hψ ha
  refine ⟨a' / a, div_ne_zero (trace_mul_ne_zero hψ' ha') h0, ?_⟩
  refine ext_of_inf hψ'.1 (hψ.1.comp (continuous_const.mul continuous_id)) ψ'.map_add_eq_mul
    (fun x y => by rw [mul_add, ψ.map_add_eq_mul]) hψ'.2.2.1 (fun x => by rw [← map_mul, hψ.2.2.1]) fun x => ?_
  have e : algebraMap F (AF F) (a' / a) * pairA F (algebraMap F _ x) 0 =
      pairA F (algebraMap F _ (a' / a * x)) 0 :=
    Prod.ext (map_mul (algebraMap F (Ainf F)) _ _).symm (mul_zero _)
  rw [e, ha, ha', ← mul_assoc, mul_div_cancel₀ _ h0]

end GlobalTheory.AdeleCharTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOpenKer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff Topology

namespace GlobalTheory.Mem.ThetaClosed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.WeilTieCheck GlobalTheory.FockCompare

variable {D : D7}

theorem exists_open_ker {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    {ψ : AddChar (AF D.host.F) ℂ} (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1) (φ : G →+ AF D.host.F)
    (hφ : Continuous φ) :
    ∃ K : AddSubgroup G, IsOpen (K : Set G) ∧ ∀ w ∈ K, fstA D.host.F (φ w) = 0 → ψ (φ w) = 1 := by
  let q : G →+ AF D.host.F :=
    (AddMonoidHom.inr (Ainf D.host.F) (Af D.host.F)).comp ((AddMonoidHom.snd (Ainf D.host.F) (Af D.host.F)).comp φ)
  let K : AddSubgroup G :=
    { carrier := {w | ψ (q w) = 1}
      zero_mem' := by
        show ψ _ = 1
        rw [map_zero, ψ.map_zero_eq_one]
      add_mem' := fun {a b} ha hb => by
        have ha' : ψ _ = 1 := ha
        have hb' : ψ _ = 1 := hb
        show ψ _ = 1
        rw [map_add (f := _), AddChar.map_add_eq_mul, ha', hb', one_mul]
      neg_mem' := fun {a} ha => by
        have ha' : ψ _ = 1 := ha
        show ψ _ = 1
        have := AddChar.map_add_eq_mul ψ (q a) (q (-a))
        rw [← map_add (f := _), add_neg_cancel, map_zero, ψ.map_zero_eq_one, ha', one_mul] at this
        exact this.symm }
  refine ⟨K, K.isOpen_of_mem_nhds (g := 0) ?_, fun w hw h0 => ?_⟩
  · have h1 : Continuous fun w : G => (φ w).2 := continuous_snd.comp hφ
    exact h1.continuousAt.preimage_mem_nhds (x := 0) (t := {a | ψ (pairA D.host.F 0 a) = 1})
      (by rw [map_zero]; exact GlobalTheory.FinTranslate.ker_mem_nhds hc hn)
  · have h4 : φ w = q w := Prod.ext h0 rfl
    rw [h4]
    exact hw

theorem isThetaFun_heis {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {V W : HSp D} {f : WA V W → ℂ}
    (hf : IsThetaFun ψ V W f) (u : WA V W) : IsThetaFun ψ V W (Heisenberg₂ ψ V W u f) := by
  haveI : IsTopologicalAddGroup (AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WA V W) := Pi.topologicalAddGroup
  have hc : Continuous ψ := hψ.1.1
  let φ₁ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W w u) fun a b => symplH_add_left V W a b u
  let φ₂ : WA V W →+ AF D.host.F := AddMonoidHom.mk' (fun w => symplH V W u w) fun a b => symplH_add_right V W u a b
  have c₁ : Continuous φ₁ := ThetaCont.continuous_symplH V W continuous_id continuous_const
  have c₂ : Continuous φ₂ := ThetaCont.continuous_symplH V W continuous_const continuous_id
  refine ⟨heis_quasi ψ V W u f hf.quasi, ?_, (hc.comp c₁).mul (hf.cont.comp (continuous_id.add continuous_const)),
    fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨K₁, hK₁, h₁⟩ := exists_open_ker hc hψ.1.2.1 φ₁ c₁
    obtain ⟨K₂, hK₂, h₂⟩ := exists_open_ker hc hψ.1.2.1 φ₂ c₂
    refine ⟨U ⊓ (K₁ ⊓ K₂), hU.inter (hK₁.inter hK₂), fun w hw hw' => ?_⟩
    have e₁ : ψ (symplH V W w u) = 1 := h₁ w hw.2.1 (by
      show fstA D.host.F (_ * sympl V W w u) = 0
      rw [map_mul, (sympl_parts D V W w u).2 (Or.inl hw'), mul_zero])
    have e₂ : ψ (symplH V W u w) = 1 := h₂ w hw.2.2 (by
      show fstA D.host.F (_ * sympl V W u w) = 0
      rw [map_mul, (sympl_parts D V W u w).2 (Or.inr hw'), mul_zero])
    conv_rhs => rw [← hUf w hw.1 hw']
    rw [heis_heis, heis_heis, e₁, e₂, add_comm]
  · obtain ⟨lam, hl, hlam⟩ := GlobalTheory.WeilVacMove.exists_log hψ
    let χ : (Fin k → ℝ) →+ ℂ := lam.comp (φ₁.comp L)
    have hχ : ContDiff ℝ ∞ χ := GlobalTheory.WeilVacMove.contDiff_additive χ (hl.comp (c₁.comp hL))
    have : (fun t => Heisenberg₂ ψ V W u f (w + L t)) =
        fun t => ψ (symplH V W w u) * Complex.exp (χ t) * f (w + u + L t) := by
      funext t
      have e : ψ (symplH V W (L t) u) = Complex.exp (χ t) := hlam _ (by
        show sndA D.host.F (_ * sympl V W (L t) u) = 0
        rw [map_mul, (sympl_parts D V W (L t) u).1 (Or.inl (hLf t)), mul_zero])
      rw [Heisenberg₂, symplH_add_left, AddChar.map_add_eq_mul, e, add_right_comm]
    rw [this]
    exact (contDiff_const.mul hχ.cexp).mul (hf.smooth k L hL hLf (w + u))

theorem thetaFun_closed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V W : HSp D) (f : WA V W → ℂ), (f ∈ ThS ψ V W ↔ IsThetaFun ψ V W f) ∧ (IsThetaFun ψ V W f → ∀ w₀, IsThetaFun ψ V W (Heisenberg₂ ψ V W w₀ f)) ∧ (V.rank ≠ W.rank → IsThetaFun ψ V W f → IsThetaFun ψ W V (fun x => f x.transpose)) := by
  intro D ψ hψ V W f
  refine ⟨⟨fun h => ?_, fun h => Submodule.subset_span h⟩, fun hf u => isThetaFun_heis hψ hf u,
    fun hne hf => isThetaFun_transpose ψ V W hne f hf⟩
  obtain ⟨M, hM⟩ := exists_thetaSubmodule D ψ V W
  exact (hM f).1 (Submodule.span_le.2 (fun g hg => (hM g).2 hg) h)

end GlobalTheory.Mem.ThetaClosed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueNormalizedHaarMeasureAdelicUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.VolMeasure

theorem existsUnique_isVolMeasG : ∀ (D : D7) (V : HSp D), V.SigOK →
    ∃! μ, IsVolMeasG D V (fun ρ => (V.sig (tauE D ρ)).1) (fun ρ => (V.sig (tauE D ρ)).2) μ := by
  intro D V hV
  have hτ : GlobalTheory.Mem.Vol.IsCMFam (tauE D) := GlobalTheory.CMTypePlaces.mk_tauE_bijective D
  obtain ⟨μ, hμ⟩ := GlobalTheory.Mem.VolExists.exists_isVolMeasF _ _ D.sp.cm _ (tauE D) D.cd V hτ hV
  exact ⟨μ, hμ, fun ν hν =>
    GlobalTheory.Mem.VolUnique.volMeas_unique _ _ D.sp.cm _ (tauE D) D.cd V hτ hV ν μ hν hμ⟩

end GlobalTheory.Mem.VolMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCovolumeLatticeStabiliserUnitaryRealPointsStatement
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_covolume_latticeStabiliser_unitaryRealPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∀ ν : Measure (HA (Ainf F) σ J), ν.IsHaarMeasure → ∃ Ω : Set (HA (Ainf F) σ J), MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : HA (Ainf F) σ J, ∃ γ ∈ Formalism.UG.UJ (σ : E →+* E) J, (∀ x, x ∈ L ↔ (γ : Matrix (Fin M) (Fin M) E).mulVec x ∈ L) ∧ ∃ w ∈ Ω, HA.mat (Ainf F) σ J g = Formalism.UG.bc (inclR (F := F) (Ainf F)) γ * HA.mat (Ainf F) σ J w := by
  first | exact @GlobalTheory.MixedSignature.finite_covolume_real_points | exact GlobalTheory.MixedSignature.finite_covolume_real_points | (intros; apply GlobalTheory.MixedSignature.finite_covolume_real_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussianInnerEqInvariantKernelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc GlobalTheory.OscGauss Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_inner_eq_invariantKernel : ∀ (P Q : ℕ) (Y Y' : Matrix (Ix P Q) (Fin Q) ℂ) (v φ v' φ' : Ix P Q → ℂ), IsUnit Y.toRows₂.det → IsUnit Y'.toRows₂.det → IsUnit (1 - (matA Y)ᴴ * matA Y').det → let A := matA Y; let B := matA Y'; let a : Fin P → ℂ := fun i => star (linX Y v φ (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (linX Y v φ (Sum.inr j)); let c : Fin P → ℂ := fun i => linX Y' v' φ' (Sum.inl i); let d : Fin Q → ℂ := fun j => linX Y' v' φ' (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; star (scal Y v φ) * scal Y' v' φ' * (((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c)) = ker Y v φ Y' v' φ' := by
  first | exact @GlobalTheory.OscGauss.kerAlg | exact GlobalTheory.OscGauss.kerAlg | (intros; apply GlobalTheory.OscGauss.kerAlg <;> assumption)
end

