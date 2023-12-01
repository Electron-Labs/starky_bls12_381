// BLS Native

use std::str::FromStr;

use num_bigint::BigUint;

pub fn split_to_u32() {

}

pub fn mod_sub(a: u32, b: u32) -> (u32, bool) {
    let mut borrow = false;
    if a<b {
        borrow = true;
    }
    let mut ans;
    if borrow {
       ans = ((borrow as u64) * (1u64 << 32) + (a as u64) - (b as u64)) as u32;
    } else {
       ans = a - b;
    }
    (ans, borrow)
}

// [TODO] handle case for when a[i] is 0 to begin with, might fuck up carries
pub fn big_sub(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    assert_eq!(a.len(), 12);
    assert_eq!(b.len(), 12);
    let mut result = Vec::<u32>::new();
    // Assuming a > b
    let (mut borrow, mut is_borrow) = mod_sub(a[0],b[0]);
    result.push(borrow);
    for i in 1..12  {
        if is_borrow {
            (borrow, is_borrow) = mod_sub(a[i]-1, b[i]);
        }else {
            (borrow, is_borrow) = mod_sub(a[i], b[i]);
        }
        result.push(borrow);
    }
    result
}

pub fn miller_loop_fp2(base_elm: [Vec<u32>; 2], ext_elm: [Vec<u32>;4]) {
    // logK = 4
    // XI0 = 1
    // 
}

pub fn verify_bls_signatures() -> bool {
    // Public key
    // Splits into little endian
    let pk_x = BigUint::from_str("3071902358779104425805220059913391042958977442368743450008922736970201383908820407429457646333339330346464018568299").unwrap().to_u32_digits();
    let pk_y = BigUint::from_str("208729469830998646909339719617829960147637284847029296662162145937938053125975650713155855600870449370845588704920").unwrap().to_u32_digits();

    // Hashed message in g2
    let Hm_x_1 = BigUint::from_str("377525340465127240390006870673927129435673249221760063250140335517131386743242190939209933287674151299948365589984").unwrap().to_u32_digits();
    let Hm_x_2 = BigUint::from_str("1050959494132411586723873443636085717179713480840095989211192028601018716895799746178715855146873969711260353313306").unwrap().to_u32_digits();
    let Hm_y_1 = BigUint::from_str("1131267707057668367159571747448144959495496577180002964665679138922368484682635468083328267231891238196968252631379").unwrap().to_u32_digits();
    let Hm_y_2 = BigUint::from_str("3783154323541729598398766283148329593362868413141617593978449262336941595119881847879377563302954053187852058644118").unwrap().to_u32_digits();
    // Generator
    let G_x = BigUint::from_str("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507").unwrap().to_u32_digits();
    let G_y = BigUint::from_str("1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569").unwrap().to_u32_digits();

    // Signature
    let S_x_1 = BigUint::from_str("966572263166434944599183957482752531047038993953916430862595578899059824912156165297149403978420723932172123775406").unwrap().to_u32_digits();
    let S_x_2 = BigUint::from_str("842321951799503469014964953496381065608123412078137658319961132736911642409943969612292629578043499296195717122533").unwrap().to_u32_digits();
    let mut S_y_1 = BigUint::from_str("1639805997476177777241606094884612303776858264957232458415894583607376414805753804084820168641517462543804792794779").unwrap().to_u32_digits();
    let mut S_y_2 = BigUint::from_str("3855722596444217665140296300241881837775734411784092265317102637289824807772757224642216633698428180424693166393122").unwrap().to_u32_digits();

    let bls_12_381_prime = BigUint::from_str("4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787").unwrap().to_u32_digits();

    // 1. negate Signature
    let S_y_1 = big_sub(bls_12_381_prime.clone(), S_y_1);
    let S_y_2 = big_sub(bls_12_381_prime.clone(), S_y_2);

    // 2. Miller loop





//    let pairingRes = pairing(P.pointNegate(), Hm)
//    let pairingRes2 = pairing(G, S)
    true
}

#[cfg(test)]   
mod tests {
    use std::str::FromStr;

    use num_bigint::BigUint;

    use crate::native::big_sub;

    use super::verify_bls_signatures;

    #[test]
    pub fn test1() {
        verify_bls_signatures();
    }

    #[test]
    pub fn test_big_sum() {
        let pk_x = BigUint::from_str("3071902358779104425805220059913391042958977442368743450008922736970201383908820407429457646333339330346464018568299").unwrap();
        let pk_x_u32 = pk_x.to_u32_digits();
        let S_x_1 = BigUint::from_str("966572263166434944599183957482752531047038993953916430862595578899059824912156165297149403978420723932172123775406").unwrap();
        let S_x_1_u32 = S_x_1.to_u32_digits();
        let res = big_sub(pk_x_u32, S_x_1_u32);
        assert_eq!(BigUint::new(res), pk_x-S_x_1);
    }
}