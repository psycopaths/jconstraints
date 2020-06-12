
plugins {
    `java-library`
    id("com.github.hierynomus.license") version "0.15.0"
    id("com.github.johnrengelman.shadow") version "5.2.0"
}

repositories {
    jcenter()
    mavenLocal()
    mavenCentral()
}

dependencies {

    implementation("gov.nasa:jconstraints:0.9.7-SNAPSHOT")
    implementation("io.github.tudo-aqua:cvc4-turnkey-gpl:1.7")

    testImplementation("org.testng:testng:7.0.0")
}

val test by tasks.getting(Test::class) {
    // Use TestNG for unit tests
    useTestNG()
}

license {
    header = rootProject.file("NOTICE")
    strictCheck = true
}
