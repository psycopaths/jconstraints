
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
    implementation("solver:CVC4-gpl:1.8.0")
    implementation("org.apache.commons:commons-math3:3.6.1")

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
