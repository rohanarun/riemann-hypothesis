module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.Bundle0018
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0015
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0019
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0017
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.GaloisRepExistsTotallyRealGL2
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfHRep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SphericalDecomposition.SphOfWit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DualIsConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CountVOf
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia
private theorem arith {a V E : ℕ} {s L X : ℝ} {C : ℕ} (ha : a ≤ V) (hV : (V : ℝ) ≤ 2 * E * s) (hL : 0 ≤ L)
    (hs : s * L ≤ X ^ C) (hX : 2 ≤ X) : (a : ℝ) / E * L ≤ X ^ (C + 1) := by
  have hp : 0 ≤ X ^ C := pow_nonneg (by linarith) C
  rcases Nat.eq_zero_or_pos E with rfl | hE
  · simp only [Nat.cast_zero, div_zero, zero_mul]
    exact pow_nonneg (by linarith) _
  · have hE' : (0 : ℝ) < E := by exact_mod_cast hE
    have ha' : (a : ℝ) ≤ V := by exact_mod_cast ha
    have h1 : (a : ℝ) / E ≤ 2 * s := by
      rw [div_le_iff₀ hE']
      linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hL
    have h3 := mul_le_mul_of_nonneg_left hX hp
    rw [pow_succ]
    linarith
private theorem l_mem {l : ℕ} [hl : Fact l.Prime] (c : Coef l) : ((l : ℕ) : c.O) ∈ maximalIdeal c.O := by
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
  have h : ((l : ℕ) : ℤ_[l]) ∈ maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have := map_nonunit (algebraMap ℤ_[l] c.O) _ h
  rwa [map_natCast] at this
theorem UpperTheory.V.UnitaryThreeInertia.countV_of_finiteness_duality_euler_host :
    _root_.UpperTheory.V.Aut.ThmS6_s → LemmaM → LemmaM' → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → GlobalTheory.Published.PoitouTateNormalised → HostVanE → HostXpp → _root_.UpperTheory.V.UnitaryThreeInertia.HostRigid_s → _root_.UpperTheory.V.UnitaryThreeInertia.HostNumber_s → CountV := by
  intro hS6 hM hM' hLF hLT hLE hGF hGE hPT hVan hX hRig hNum χ
  obtain ⟨K, _, _, _, hK⟩ := gaussian_field_range_eq_ker_quartic_char.1
  obtain ⟨C, hC⟩ := hNum K hK
  refine ⟨C + 1, fun h _ t _ Ω _ _ _ l hl c e h2 he _ ψ hψ hP => ?_⟩
  obtain ⟨hD, hXD⟩ := hostData_of_host h c e h2 he ψ hψ hP.2
  obtain ⟨S, A, F, hF⟩ := exists_hostFrame Ω c e ψ _ hD
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  obtain ⟨g₁, hg, hS⟩ := hS6 K hK Ω l ι c h.N e ψ _ hD S A F hF
  obtain ⟨hphi, i1, i2, i3, i4, i5, i6⟩ := hostFrame_phi hGF Ω c e ψ _ hD S A F hF
  have hOk := hostFrame_ok Ω c e ψ _ hD S A F hF
  obtain ⟨R, _, _, _, u, hu⟩ := exists_isUniv F hOk l hl.out (l_mem c) hphi g₁ hg
  obtain ⟨hfin, hB⟩ := hS R u hu
  obtain ⟨φ, hne, hsum⟩ := hC Ω l c h.N e ψ _ hD S A F hF ι g₁ hg
  obtain ⟨n, r, V, hr, hinj, hV, hle⟩ := abstract_count hM hM' (l := l) F hOk
    (hostFrame_locVan hLF hLT hLE Ω c e ψ _ hD S A F hF)
    (hostFrame_count hLF hLT hLE hGF hGE hPT Ω c e ψ _ hD S A F hF)
    (hVan Ω l c h.N e ψ _ hD S A F hF) (frame_class_one Ω c e ψ _ hD S A F hF)
    (hX Ω l c h.N e ψ _ hD _ hXD S A F hF) g₁ hg u hu hfin φ
    (fun r => _root_.UpperTheory.V.Aut.BPrime_s K ι fun s => (r (toGS Ω _ s)).mat) hB
    (fun r h1 h2 h3 => ⟨hRig K hK Ω l c h.N e ψ _ hD S A F hF ι g₁ hg r h1 h3, hne r h1 h2 h3⟩)
  have hlen := vlen_le Ω c e ψ _ hD S A F hF V hV
  have hX2 : (2 : ℝ) ≤ (l : ℝ) * h.N * e := by
    have : 2 * 1 * 1 ≤ l * h.N * e := Nat.mul_le_mul (Nat.mul_le_mul hl.out.two_le h.N_pos) he
    exact_mod_cast this
  refine ⟨ne_top_of_le_ne_top (ENat.coe_ne_top V) hlen, ?_⟩
  exact arith (ENat.toNat_le_of_le_coe hlen) hle (Real.log_natCast_nonneg l) (hsum n r hr hinj) hX2
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EGIndAutCs
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Sd UpperTheory.V.Base UpperTheory.V.Z.Bc UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
private theorem infOf_two (m : Fin 2 → ℤ) : infOf m = {1 / 2 + (m 0 : ℂ), 1 / 2 + (m 1 : ℂ)} := by
  have e : (((2 : ℕ) : ℂ) - 1) / 2 = 1 / 2 := by norm_num
  rw [infOf, e]
  rfl
private theorem infOf_add {m m' : Fin 2 → ℤ} (h : Function.Injective ![m 0, m 1, m' 0, m' 1]) :
    (infOf m + infOf m').Nodup ∧ ∀ z ∈ infOf m + infOf m', ∃ n : ℤ, z = (n : ℂ) + (((4 : ℕ) : ℂ) - 1) / 2 := by
  have e : infOf m + infOf m' = Finset.univ.val.map fun i => 1 / 2 + ((![m 0, m 1, m' 0, m' 1] i : ℤ) : ℂ) := by
    rw [infOf_two, infOf_two]
    rfl
  rw [e]
  refine ⟨Finset.univ.nodup.map fun i j hij => h (Int.cast_injective (add_left_cancel hij)), fun z hz => ?_⟩
  obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
  exact ⟨![m 0, m 1, m' 0, m' 1] i - 1, by push_cast; ring⟩
private theorem tw_back {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]
    (R : G F Ω →* GL (Fin 4) (Qbar l)) : R = tw (tw R (cycBar F Ω l)⁻¹) (cycBar F Ω l ^ (1 : ℤ) * 1) := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, ← Units.val_mul]
  simp
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutCs_of_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') (h : IndCs) : IndAutCs := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ h2 l _ ι π r hatt hm hb R hR H
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
  obtain ⟨P, hfin, hinf⟩ := h K M h2 π hm hb
  have key : IsAutC ι (tw R (cycBar K Ω l)⁻¹) := by
    refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun φ => ?_, attInd K M Ω h2 l ι r R (CG.mk π).HasSat (CG.mk P).HasSat (fun _ _ _ h h' => h.unique h') (fun _ _ _ h h' => h.unique h') hatt hfin hR H⟩
    obtain ⟨m, m', τ, τ', hne, rfl, e, hv, hv', hinj⟩ := hm φ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ τ' _ _ hne e.symm hv hv')]
    exact infOf_add hinj
  rw [tw_back R]
  exact _root_.UpperTheory.V.Sd.twist_conjugate_selfDual hP K Ω l ι 4 _ _ ((_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hP K Ω l ι).1 1 1 (by simp)) key
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExRS
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.Gal.SV
theorem exRS_alt :
    _root_.UpperTheory.V.Af.Hypotheses' → ExRS := by
  intro P F Ω _ _ _ _ _ _ l _ ι n _ hn π χ hreg hpol
  obtain ⟨r, wt, HT, H⟩ := _root_.UpperTheory.Gal.SV.gr2S' P.galR F Ω l ι n hn π χ hreg hpol
  have key := H.frob
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  refine ⟨r, wt, HT, H, ⟨H.ss, ?_⟩, fun r' hr' ha => galRS_iso H ha.1 ?_⟩
  · filter_upwards [sat_ae_of_smooth (_root_.UpperTheory.V.Af.satake_local_of_printed_results P) π.finPart hsm fun w =>
      let ⟨⟨σ, hσ⟩, hiso⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F n π w
      ⟨σ, hiso σ hσ⟩, eventually_not_mem F l] with w ⟨B, hB⟩ hw
    exact ⟨B, hB, key w hw B hB⟩
  · refine _root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results P F Ω l ι n r r' H.cont hr' H.ss ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw
    exact ⟨_, key w hw B hB, hf⟩
end UpperTheory.Gal.SV
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsSat
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual Polynomial UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd Matrix
open GlobalTheory.CuspRep (SmIrr Af invT finId pFin locGL finGL GA chiDet)
namespace UpperTheory.Esk.HeckeRepresentationSatake
section Proj
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ}
theorem exists_sat_alt (P : _root_.UpperTheory.V.Af.Hypotheses') (π : TR.CuspSub F a) (w : HeightOneSpectrum (𝓞 F))
    (h : HasFixed (π.locRep w) (GlobalTheory.LFun.KGL w (n := a))) : ∃ B, π.HasSat w B := by
  obtain ⟨⟨σ, hσ⟩, h2⟩ := _root_.UpperTheory.V.Af.local_comp_real_of_printed_results P F a π w
  have hi := h2 σ hσ
  obtain ⟨h3, h4⟩ := _root_.UpperTheory.V.Af.satake_local_of_printed_results P F a w σ
  obtain ⟨x, hx0, hx⟩ := h
  obtain ⟨B, hB⟩ := h3 (GlobalTheory.CuspRep.LocSph.exists_fixed_of_mem_iSup (π.locRep w) σ.ρ σ.irred
    (fun f : {f : σ.V →ₗ[ℂ] π.V // ∀ g v, f (σ.ρ g v) = π.finPart (locGL F a w g) (f v)} => f.1) (fun f => f.2)
    (GlobalTheory.LFun.KGL w (n := a) : Set _) x hx0 hx (hi.2 ▸ Submodule.mem_top))
  exact ⟨B, (h4 _ _ hi B).2 hB⟩
end Proj
section Loc
open GlobalTheory.LFun Formalism.UG
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
end Loc
section Inf
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
open GlobalTheory.HeckeGal.Model GlobalTheory.Mem.Chr.CharModel
end Inf
section Sign
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
end Sign
theorem _root_.UpperTheory.Esk.pf_HRep_alt : _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.Esk.HCap → UpperTheory.Esk.HRep := by
  intro P hC
  unfold UpperTheory.Esk.HCap at hC
  unfold UpperTheory.Esk.HRep
  intro F _ _ _ k hk t c ω hω φ lam hφ hne heig hcusp
  obtain ⟨h1, hcap⟩ := hC F (fun v => k + 2 * t v) c ω hω φ hφ
  obtain ⟨π₀, ψ, hψ, h0, hz⟩ := proj hne (P.ssR F 2 φ hcusp ⟨0, by rw [h1, zero_smul]⟩)
  set ν := GlobalTheory.HeckeGal.Model.absPow F (1 - (k : ℝ) / 2) with hν
  obtain ⟨hν1, hν2, -⟩ := GlobalTheory.HeckeGal.Model.absPow_isAbsPow F (1 - (k : ℝ) / 2)
  rw [← hν] at hν1 hν2
  have hnorm (w : Pl F) : normV w = Ideal.absNorm w.asIdeal := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq : ∀ w : Pl F, (0 : ℝ) < normV w := fun w =>
    Nat.cast_pos.2 (zero_lt_one.trans (by rw [hnorm]; exact NumberField.HeightOneSpectrum.one_lt_absNorm w))
  have hν3 : ∀ w, ((ν.val w : ℂˣ) : ℂ) = (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) := fun w => by
    rw [hν2, Complex.ofReal_cpow (hq w).le, ← Complex.ofReal_neg, neg_sub]
    rw [hnorm]
    push_cast
    rfl
  set π := π₀.twist ν
  set x₀ : π₀.V := ⟨ψ, hψ⟩
  set T := π₀.toTwist ν
  have hx0 : T x₀ ≠ 0 := (map_ne_zero_iff _ T.injective).2 fun e => h0 (congrArg Subtype.val e)
  have hact : ∀ w g y, π.locRep w g (T y) = ((ν.loc w (GeneralLinearGroup.det g) : ℂˣ) : ℂ) • T (π₀.locRep w g y) :=
    fun w g y => (TR.CuspSub.finPart_toTwist ν _ y).trans (by rw [TR.CuspSub.chiDet_locGL]; rfl)
  have hloc : ∀ w g (a : ℂ), locSm F w g φ = a • φ → π₀.locRep w g x₀ = a • x₀ := fun w g a h =>
    Subtype.ext (hz _ (fun V hV => hV (.fin (locGL F 2 w g))) a h)
  have hfix₀ : ∀ w, x₀ ∈ Hi.fixd (π₀.locRep w) (K1 w (c w)) := fun w u hu =>
    (hloc w u 1 ((hφ.level w u hu).trans (one_smul _ _).symm)).trans (one_smul _ _)
  have hfix : ∀ w, T x₀ ∈ Hi.fixd (π.locRep w) (K1 w (c w)) := fun w u hu => by
    rw [hact, hν1 w _ (unit_det w hu), hfix₀ w u hu, Units.val_one, one_smul]
  have hU : ∀ w, Uop w (π.locRep w) (c w) (T x₀) = lam w • T x₀ := fun w => by
    have h2 := hz (Sd.hk k w (c w)) (fun V hV y hy => V.smul_mem _
      (finsum_induction (fun z : Module.End ℂ (TR.Sm F 2) => z y ∈ V) V.zero_mem (fun _ _ => V.add_mem)
        fun q => hV (.fin _) y hy)) _ (heig w)
    have h3 := uop_map w (ρ' := locSm F w) π₀.V.subtype 1 (fun g y => (one_smul _ _).symm) (c w) x₀ (hfix₀ w)
      fun u hu => congrArg Subtype.val (hfix₀ w u hu)
    refine (uop_map w T.toLinearMap (ν.loc w) (hact w) (c w) x₀ (hfix₀ w) (hfix w)).trans ?_
    rw [LinearEquiv.coe_coe, ← map_smul T, ← map_smul T]
    refine congrArg T (Subtype.ext ?_)
    refine Eq.trans ?_ h2
    change ((ν.val w : ℂˣ) : ℂ) • π₀.V.subtype (Uop w (π₀.locRep w) (c w) x₀) =
      (((normV w : ℝ) ^ ((k : ℝ) / 2 - 1) : ℝ) : ℂ) • Uop w (locSm F w) (c w) (π₀.V.subtype x₀)
    rw [h3, hν3]
    exact congrArg _ (one_smul _ _).symm
  have hZ : ∀ w, π.locRep w (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) (T x₀) =
      (((ω * ν * ν).val w : ℂˣ) : ℂ) • T x₀ := fun w => by
    rw [hact, hloc w _ (ω.val w : ℂˣ) (Subtype.ext (funext fun g => by
      change φ.1 (g * finGL F 2 (locGL F 2 w _)) = _
      rw [fin_scalar, ← GlobalTheory.CuspRep.scalar_comm, hφ.cent]
      rfl)), map_smul, smul_smul,
      show GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 2) (atFin w (unif w))) =
        atFin w (unif w) * atFin w (unif w) from Units.ext (by simp [sq]), map_mul, mul_comm, ← Units.val_mul, ← mul_assoc]
    rfl
  have hsat : ∀ w, (∀ u ∈ GlobalTheory.LFun.KGL w (n := 2), π.locRep w u (T x₀) = T x₀) → ∃ α β : ℂˣ, π.HasSat w {α, β} ∧
      Uop w (π.locRep w) 0 (T x₀) = ((((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) * (α + β)) • T x₀ ∧
      α * β = (ω * ν * ν).val w := fun w h => by
    obtain ⟨B, hB⟩ := _root_.UpperTheory.Esk.HeckeRepresentationSatake.exists_sat_alt P.toClassicalTheorems π w ⟨_, hx0, h⟩
    obtain ⟨α, β, rfl, h2, h3⟩ := sat_two w (hB.2 _ (GlobalTheory.LGrp.mem_fixed.2 h) hx0)
    exact ⟨α, β, hB, h2, Units.ext (smul_left_injective ℂ hx0 (h3.symm.trans (hZ w)))⟩
  have hinf : ∀ v, π.HasInfChar v (infOf ![(t v : ℤ), 1 - (k : ℤ) - t v]) := fun v => by
    have h2 : π₀.HasInfChar v {(((k + 2 * t v : ℕ) : ℂ) - 1) / 2, -((((k + 2 * t v : ℕ) : ℂ) - 1) / 2)} :=
      ⟨rfl, fun u => cap_all π₀ hψ h0 v u _ (by
        rw [hz _ (fun V hV => TR.Zalg_stable (fun X => hV (.lie X)) (Algebra.subset_adjoin ⟨v, u, rfl⟩)) _ (hcap v u)]
        simp [sub_eq_add_neg])⟩
    convert h2.twist ν using 1
    rw [hν, expo_abs]
    simp only [infOf, Fin.univ_val_map, List.ofFn_succ, List.ofFn_zero, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton]
    change _ ::ₘ ({_} : Multiset ℂ) = _
    refine congrArg₂ _ ?_ (congrArg _ ?_) <;> simp <;> ring
  refine ⟨π, fun v => ⟨_, hinf v, ?_, fun z hz => ?_⟩, ⟨ω * ν * ν, fun v v' => ?_, ?_⟩, hinf,
    fun w => ⟨_, hx0, hfix w, hU w⟩, fun w hw => ?_⟩
  · refine Multiset.Nodup.map (fun i j e => ?_) Finset.univ.nodup
    have e' : ![(t v : ℤ), 1 - (k : ℤ) - t v] i = ![(t v : ℤ), 1 - (k : ℤ) - t v] j := by exact_mod_cast add_left_cancel e
    fin_cases i <;> fin_cases j <;> simp at e' ⊢ <;> omega
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
    exact ⟨_, add_comm _ _⟩
  · change ω.locInf v (-1) * ν.locInf v (-1) * ν.locInf v (-1) =
      ω.locInf v' (-1) * ν.locInf v' (-1) * ν.locInf v' (-1)
    simp only [hν, sign_abs, mul_one]
    exact Units.ext ((sign_hol hφ hne v).trans ((sign_eq k (t v)).trans ((sign_eq k (t v')).symm.trans (sign_hol hφ hne v').symm)))
  · obtain ⟨B, hl, hr, hf, hc, hX⟩ := P.gkR F 2 π
    refine TR.CuspSub.isSelfDualBy_of_iso B hl hr hf hc hX (P.smoR F 2 one_le_two _ _ ?_)
    filter_upwards [GlobalTheory.CuspRep.LocSph.eventually_mem ((π.isSmooth_finPart (T x₀)).mem_nhds
        (show π.finPart 1 (T x₀) = T x₀ by rw [map_one]; rfl)),
      Filter.eventually_cofinite.2 (GlobalTheory.Mem.UnrAe.finite_ramified (ω * ν * ν))] with w hw hu
    obtain ⟨α, β, h2, -, h3⟩ := hsat w (by rintro _ ⟨g, rfl⟩; exact hw g)
    have e : (({α, β} : Multiset ℂˣ).map (·⁻¹)).map (· * (ω * ν * ν).val w) = {α, β} := by
      rw [← h3, Multiset.pair_comm α β]
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, inv_mul_cancel_left]
      rw [mul_comm α β, inv_mul_cancel_left]
      exact Multiset.pair_comm α β
    exact ⟨_, h2, e ▸ h2.dual.twist hu⟩
  · obtain ⟨α, β, h2, h3, h4⟩ := hsat w (by have := hfix w; rwa [hw, iwahori_level_zero_eq] at this)
    refine ⟨_, h2, ?_⟩
    have h5 := hU w
    rw [hw] at h5
    have h6 := smul_left_injective ℂ hx0 (h5.symm.trans h3)
    have h7 : (α : ℂ) * β = (ω.val w : ℂˣ) * (ν.val w : ℂˣ) * (ν.val w : ℂˣ) := congrArg Units.val h4
    set r : ℂ := (((normV w : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) with hr
    have h8 : r * r * ((ν.val w : ℂˣ) * (ν.val w : ℂˣ)) = (normV w : ℂ) ^ (k - 1) := by
      rw [hν3, hr, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.rpow_add (hq w),
        ← Real.rpow_add (hq w), ← Real.rpow_add (hq w),
        show (1 / 2 + 1 / 2 + ((k : ℝ) / 2 - 1 + (k / 2 - 1))) = ((k - 1 : ℕ) : ℝ) by
          rw [Nat.cast_sub (by omega)]; push_cast; ring, Real.rpow_natCast]
      simp
    have h9 : algSat 2 (normV w) {α, β} = {r * α, r * β} := by
      simp only [algSat, hr, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton]
      norm_num
    rw [h9, h6, ← h8, show (ω.val w : ℂˣ) * (r * r * (((ν.val w : ℂˣ) : ℂ) * (ν.val w : ℂˣ))) = r * α * (r * β) by
      linear_combination (-(r * r)) * h7]
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
      Multiset.prod_singleton, map_mul, map_add]
    ring
end UpperTheory.Esk.HeckeRepresentationSatake
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.FrobRoot
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
namespace UpperTheory.V.Z.Kato.WeilSphericalRecords
theorem frobRoot_alt : _root_.UpperTheory.V.Af.Hypotheses' → LocQ → FrobRoot := by
  intro P hQ l _ Ω _ _ _ ι e V A κ g hl he hc hirr hdet hA hex hatt hgM σ hσ
  obtain ⟨π, hreg, hπ, hsat⟩ := _root_.GlobalTheory.T.exists_cuspidal_attached_satake_eq_hecke_poly_of_not_dvd P e g l Ω ι V he hatt hgM
  obtain ⟨v, hv, hlv⟩ := hA
  obtain ⟨B, hB, hpoly⟩ := hsat v hlv
  obtain ⟨b, hb, hrel⟩ :=
    (hQ l hl Ω ι e he V π hc hirr hdet hreg hπ v A κ hlv hv hex (Or.inr ⟨B, hB⟩)).2 B hB σ hσ
  refine ⟨(l : ℂ) ^ e * b, ?_, Or.inr ?_⟩
  · rw [← hpoly, Polynomial.IsRoot, Polynomial.eval_multiset_prod]
    refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨_, Multiset.mem_map_of_mem _ hb, ?_⟩)
    simp
  · refine (eq_inv_of_mul_eq_one_left ?_).symm
    rw [zpow_natCast] at hrel
    linear_combination hrel
end UpperTheory.V.Z.Kato.WeilSphericalRecords
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.GuIrrCaseT
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open NumberField Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.CuspRep

noncomputable section

namespace GuIrrCaseTDualProof

open Matrix GlobalTheory.ContraPair

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

private def phiOp (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) : Module.End ℂ (Sm L a) :=
  act (.fin (PhiU a (Af L))) * act (.cpt (PhiK L a))

omit [NumberField L] [IsCMField L] in
private theorem barK_barK (k : Kinf L a) : barK (barK k) = k := Subtype.ext (by
  ext i j : 1
  exact star_star _)

private theorem fin_cpt (k : GL (Fin a) (Af L)) (u : Kinf L a) :
    act (.cpt u) * act (.fin k) = act (.fin k) * act (Op.cpt u : Op L a) := by
  change rt L a _ * rt L a _ = rt L a _ * rt L a _
  rw [← map_mul, ← map_mul]
  exact congrArg _ (infGL_comm _ _)

private theorem phiOp_mul (o : Op L a) : phiOp L a * act (invTOp (conjOp o)) = act (thetaOp o) * phiOp L a := by
  cases o with
  | fin k =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    rw [mul_assoc, fin_cpt, ← mul_assoc, ← mul_assoc]
    congr 1
    change finRep L a _ * finRep L a _ = finRep L a _ * finRep L a _
    rw [← map_mul, ← map_mul]
    congr 1
    change _ = PhiU a (Af L) * _ * (PhiU a (Af L))⁻¹ * _
    rw [inv_mul_cancel_right]
    rfl
  | cpt k =>
    simp only [phiOp, conjOp, invTOp, thetaOp, barK_barK]
    rw [← mul_assoc, fin_cpt, mul_assoc, mul_assoc]
    congr 1
    change cptRep L a _ * cptRep L a _ = cptRep L a _ * cptRep L a _
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  | lie X =>
    simp only [phiOp, conjOp, invTOp, thetaOp]
    have h1 := GlobalTheory.CapAdInv.rt_lie (Unitary.toUnits (PhiK L a)) (-(Matrix.of X)ᴴ)
    have h2 := lie_rt_fin (E := L) (toL (-(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ)))
      (PhiU a (Af L))
    have e : Unitary.toUnits (PhiK L a) = PhiU a (Cinf L) := Units.ext rfl
    have e2 : (Unitary.toUnits (PhiK L a)).val * (-(Matrix.of X)ᴴ) * ((Unitary.toUnits (PhiK L a))⁻¹).val =
        -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) := by
      rw [e, mul_neg, neg_mul]; rfl
    rw [e2] at h1
    rw [mul_assoc, ← mul_assoc (act (Op.lie _))]
    exact (congrArg (act (.fin (PhiU a (Af L))) * ·) h1).trans ((mul_assoc _ _ _).symm.trans
      (congrArg (· * _) h2.symm))

private theorem dualIsConj_of_isCsd {π : CuspSub L a} (h : Paired π π invTOp) (hc : π.IsCsd) : DualIsConj π := by
  obtain ⟨B, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨T, hT⟩ := hc
  let P : Module.End ℂ π.V := π.op (.fin (PhiU a (Af L))) * π.op (.cpt (PhiK L a))
  let Q : Module.End ℂ π.V := π.op (.cpt (PhiK L a)⁻¹) * π.op (.fin (PhiU a (Af L))⁻¹)
  have f1 : ∀ k k' : GL (Fin a) (Af L), k * k' = 1 → ∀ φ, π.op (.fin k) (π.op (.fin k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (finRep L a k * finRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  have f2 : ∀ k k' : Kinf L a, k * k' = 1 → ∀ φ, π.op (.cpt k) (π.op (.cpt k') φ) = φ := fun k k' e φ =>
    Subtype.ext (by
      change (cptRep L a k * cptRep L a k') φ.1 = φ.1
      rw [← map_mul, e, map_one]; rfl)
  let Pe : π.V ≃ₗ[ℂ] π.V := LinearEquiv.ofLinearMap P Q
    (LinearMap.ext fun φ => by simp [P, Q, f1, f2]) (LinearMap.ext fun φ => by simp [P, Q, f1, f2])
  let S := Pe.trans T
  have hS : ∀ o φ, S (π.op (invTOp (conjOp o)) φ) = π.op o (S φ) := fun o φ => by
    change T _ = π.op o (T _)
    rw [← hT]
    exact congrArg T (Subtype.ext (LinearMap.congr_fun (phiOp_mul o) φ.1))
  have hS' : ∀ o φ, S.symm (π.op o φ) = π.op (invTOp (conjOp o)) (S.symm φ) := fun o φ => by
    rw [LinearEquiv.symm_apply_eq, hS, LinearEquiv.apply_symm_apply]
  refine ⟨B.flip ∘ₗ S.symm.toLinearMap, fun φ h => ?_, fun ψ h => h1 ψ fun x => ?_, fun k φ ψ => ?_, fun k φ ψ => ?_,
    fun X φ ψ => ?_⟩
  · exact (map_eq_zero_iff _ S.symm.injective).1 (h2 _ h)
  · simpa using h (S x)
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h3 _ _ _
  · change B _ (S.symm _) = B _ (S.symm _)
    rw [hS']; exact h4 _ _ _
  · change B _ (S.symm _) + B _ (S.symm _) = 0
    rw [hS', add_comm]; exact h5 _ _ _

end GuIrrCaseTDualProof

section
open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem spehInf_one' (m : Multiset ℂ) : spehInf 1 m = m := by
  simp [spehInf]
private theorem satTot_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (S : Fin 1 → Multiset ℂˣ) :
    satTot w (fun _ => 1) S = S 0 := by
  simp [satTot, GlobalTheory.WeilDeligne.qPow_zero]
theorem UpperTheory.V.Z.Win.Gu.irrCaseT_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → IrrCaseT := by
  intro PH E Ω _ _ _ _ _ _ l _ ι n hn1 π hπ c a d hn P ρ m σ H hsp hsplit hun hc hd r hr hF
  subst hc
  obtain rfl : d = fun _ => 1 := funext hd
  obtain rfl : a = fun _ => n := funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa using hn
  have hw : ∀ φ lam, HasWeightAt π φ lam → (P 0).HasInfChar φ (infOfWeight lam) := fun φ lam h => by
    have e := H.weight φ lam h
    rw [Fin.sum_univ_one, spehInf_one'] at e
    exact e ▸ H.inf 0 φ
  refine ⟨P 0, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, GuIrrCaseTDualProof.dualIsConj_of_isCsd (PH.toClassicalTheorems.litN.aut.gk E _ (P 0)) (H.csd 0),
    ⟨hr, hF.mono fun w ⟨S, h1, h2⟩ => ⟨S 0, h1 0, satTot_one w S ▸ h2⟩⟩, hw, fun w h => hun w h 0, fun w hs τ hτ => ?_⟩
  · obtain ⟨lam, hl⟩ := _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E _ hn1 π hπ τ
    rw [CG.HasInfChar.infChar_eq (π := CG.mk (P 0)) (hw τ lam hl)]
    refine ⟨nodup_infOfWeight lam, fun z hz => ?_⟩
    rw [infOfWeight, Multiset.mem_map] at hz
    obtain ⟨j, -, rfl⟩ := hz
    exact ⟨lam.w j - (j : ℕ), by push_cast; ring⟩
  · obtain ⟨e₁⟩ := PositivityTheory.AutomorphicGaloisHodgeTate.SaturatedBaseChange.oneFactor E w n hn (ρ 0 w) (σ · w) (hsp 0 w)
    obtain ⟨e₂⟩ := LocUniq.isLocComp_unique (P 0) w _ _ (H.loc 0 w) hτ
    exact GlobalTheory.BaseChangeBridge.isCompAlong_of_equiv (e₁.trans e₂).toLinearEquiv
      (fun g x => LinearMap.congr_fun ((e₁.trans e₂).toIntertwiningMap.isIntertwining' g) x) τ.irred (hsplit w hs)
end
end
end

